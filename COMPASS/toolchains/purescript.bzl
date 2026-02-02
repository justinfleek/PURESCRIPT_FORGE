# toolchains/purescript.bzl
#
# PureScript compilation rules for Buck2 with Nix toolchain integration.
#
# PureScript compiles to JavaScript, which runs on Node.js.
# This enables type-safe frontend and CLI code that shares types with
# Lean4 proofs via code generation.
#
# Key features:
#   - purescript_library: Build a PureScript library (.js output)
#   - purescript_binary: Build a Node.js executable
#   - purescript_test: Run PureScript tests
#
# Configuration (in .buckconfig):
#   [purescript]
#   purs = /path/to/purs           # PureScript compiler
#   spago = /path/to/spago         # Package manager
#   esbuild = /path/to/esbuild     # Bundler
#
# Usage:
#   purescript_library(
#       name = "types",
#       srcs = glob(["src/**/*.purs"]),
#       deps = [],
#   )

# ═══════════════════════════════════════════════════════════════════════════════
# PROVIDERS
# ═══════════════════════════════════════════════════════════════════════════════

PurescriptLibraryInfo = provider(fields = {
    "output_dir": provider_field(Artifact | None, default = None),
    "lib_name": provider_field(str, default = ""),
    "deps": provider_field(list, default = []),
    "modules": provider_field(list, default = []),  # List of module names
})

PurescriptToolchainInfo = provider(fields = {
    "purs": provider_field(str),
    "spago": provider_field(str | None, default = None),
    "node": provider_field(str),
    "esbuild": provider_field(str | None, default = None),
})

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

def _get_purs() -> str:
    """Get purs compiler path from config."""
    path = read_root_config("purescript", "purs", None)
    if path == None:
        fail("""
purs compiler not configured.

Configure your toolchain via Nix:

    [purescript]
    purs = /nix/store/.../bin/purs
    spago = /nix/store/.../bin/spago
    node = /nix/store/.../bin/node
    esbuild = /nix/store/.../bin/esbuild

Then run: nix develop
""")
    return path

def _get_spago() -> str | None:
    """Get spago package manager path from config."""
    return read_root_config("purescript", "spago", None)

def _get_node() -> str:
    """Get node.js path from config."""
    path = read_root_config("purescript", "node", None)
    if path == None:
        fail("node not configured. See [purescript] section in .buckconfig")
    return path

def _get_esbuild() -> str | None:
    """Get esbuild bundler path from config."""
    return read_root_config("purescript", "esbuild", None)

# ═══════════════════════════════════════════════════════════════════════════════
# PURESCRIPT LIBRARY RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _purescript_library_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    Build a PureScript library.
    
    Compiles PureScript source files to JavaScript modules.
    The output directory structure matches PureScript's module hierarchy.
    """
    purs = _get_purs()
    
    if not ctx.attrs.srcs:
        return [DefaultInfo(), PurescriptLibraryInfo()]
    
    # Output directory for compiled JS
    output_dir = ctx.actions.declare_output("output", dir = True)
    
    # Collect dependency output directories
    dep_dirs = []
    for dep in ctx.attrs.deps:
        if PurescriptLibraryInfo in dep:
            info = dep[PurescriptLibraryInfo]
            if info.output_dir:
                dep_dirs.append(info.output_dir)
    
    # Build purs compile command
    script_parts = ["set -e"]
    script_parts.append("mkdir -p $OUTPUT_DIR")
    
    # Compile command
    compile_cmd = [purs, "compile"]
    compile_cmd.extend(ctx.attrs.purs_flags)
    compile_cmd.extend(["-o", "$OUTPUT_DIR"])
    
    # Add sources
    for src in ctx.attrs.srcs:
        compile_cmd.append(cmd_args(src))
    
    # Add dependency sources (PureScript needs all sources, not just .js)
    for dep_dir in dep_dirs:
        compile_cmd.append(cmd_args(dep_dir, "/**/*.js", delimiter = ""))
    
    script_parts.append(cmd_args(compile_cmd, delimiter = " "))
    
    script = cmd_args(script_parts, delimiter = "\n")
    
    cmd = cmd_args(
        "/bin/sh", "-c",
        cmd_args(
            "OUTPUT_DIR=", output_dir.as_output(),
            " && ", script,
            delimiter = "",
        ),
    )
    
    hidden = list(ctx.attrs.srcs)
    for dep_dir in dep_dirs:
        hidden.append(dep_dir)
    
    ctx.actions.run(
        cmd_args(cmd, hidden = hidden),
        category = "purs_compile",
        identifier = ctx.attrs.name,
        local_only = True,
    )
    
    # Extract module names from source files
    modules = []
    for src in ctx.attrs.srcs:
        # Foo/Bar.purs -> Foo.Bar
        path = src.short_path
        if path.endswith(".purs"):
            module = path.removesuffix(".purs").replace("/", ".")
            modules.append(module)
    
    return [
        DefaultInfo(default_output = output_dir),
        PurescriptLibraryInfo(
            output_dir = output_dir,
            lib_name = ctx.attrs.name,
            deps = ctx.attrs.deps,
            modules = modules,
        ),
    ]

purescript_library = rule(
    impl = _purescript_library_impl,
    attrs = {
        "srcs": attrs.list(attrs.source(), default = [], doc = "PureScript source files (.purs)"),
        "deps": attrs.list(attrs.dep(), default = [], doc = "PureScript library dependencies"),
        "purs_flags": attrs.list(attrs.string(), default = [], doc = "Additional purs compiler flags"),
    },
)

# ═══════════════════════════════════════════════════════════════════════════════
# PURESCRIPT BINARY RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _purescript_binary_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    Build a PureScript executable (Node.js bundle).
    
    Compiles PureScript sources and bundles with esbuild for Node.js.
    """
    purs = _get_purs()
    node = _get_node()
    esbuild = _get_esbuild()
    
    if not ctx.attrs.srcs:
        fail("purescript_binary requires at least one source file")
    
    # Intermediate output directory
    output_dir = ctx.actions.declare_output("output", dir = True)
    
    # Final bundled executable
    exe = ctx.actions.declare_output(ctx.attrs.name + ".js")
    
    # Collect dependency output directories
    dep_dirs = []
    for dep in ctx.attrs.deps:
        if PurescriptLibraryInfo in dep:
            info = dep[PurescriptLibraryInfo]
            if info.output_dir:
                dep_dirs.append(info.output_dir)
    
    script_parts = ["set -e"]
    script_parts.append("mkdir -p $OUTPUT_DIR")
    
    # Compile
    compile_cmd = [purs, "compile"]
    compile_cmd.extend(ctx.attrs.purs_flags)
    compile_cmd.extend(["-o", "$OUTPUT_DIR"])
    
    for src in ctx.attrs.srcs:
        compile_cmd.append(cmd_args(src))
    
    for dep_dir in dep_dirs:
        compile_cmd.append(cmd_args(dep_dir, "/**/*.js", delimiter = ""))
    
    script_parts.append(cmd_args(compile_cmd, delimiter = " "))
    
    # Bundle with esbuild or create simple entry point
    main_module = ctx.attrs.main if ctx.attrs.main else "Main"
    
    if esbuild:
        # Use esbuild to bundle
        bundle_cmd = [
            esbuild,
            "--bundle",
            "--platform=node",
            "--format=cjs",
            cmd_args("--outfile=", exe.as_output(), delimiter = ""),
            "$OUTPUT_DIR/{}/index.js".format(main_module.replace(".", "/")),
        ]
        script_parts.append(cmd_args(bundle_cmd, delimiter = " "))
    else:
        # Create simple Node.js entry point
        entry_content = """
#!/usr/bin/env node
require('./{}/index.js').main();
""".format(main_module.replace(".", "/"))
        script_parts.append(cmd_args(
            "cat > ", exe.as_output(), " << 'EOF'\n", entry_content, "EOF",
            delimiter = "",
        ))
        script_parts.append(cmd_args("chmod +x", exe.as_output(), delimiter = " "))
    
    script = cmd_args(script_parts, delimiter = "\n")
    
    cmd = cmd_args(
        "/bin/sh", "-c",
        cmd_args(
            "OUTPUT_DIR=", output_dir.as_output(),
            " && ", script,
            delimiter = "",
        ),
    )
    
    hidden = list(ctx.attrs.srcs)
    for dep_dir in dep_dirs:
        hidden.append(dep_dir)
    
    ctx.actions.run(
        cmd_args(cmd, hidden = hidden),
        category = "purs_bundle",
        identifier = ctx.attrs.name,
        local_only = True,
    )
    
    # Run command uses node
    run_cmd = cmd_args(node, exe)
    
    return [
        DefaultInfo(
            default_output = exe,
            sub_targets = {
                "output": [DefaultInfo(default_outputs = [output_dir])],
            },
        ),
        RunInfo(args = run_cmd),
    ]

purescript_binary = rule(
    impl = _purescript_binary_impl,
    attrs = {
        "srcs": attrs.list(attrs.source(), default = [], doc = "PureScript source files (.purs)"),
        "deps": attrs.list(attrs.dep(), default = [], doc = "PureScript library dependencies"),
        "main": attrs.option(attrs.string(), default = None, doc = "Main module (default: Main)"),
        "purs_flags": attrs.list(attrs.string(), default = [], doc = "Additional purs compiler flags"),
    },
)

# ═══════════════════════════════════════════════════════════════════════════════
# PURESCRIPT TEST RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _purescript_test_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    Build and run PureScript tests.
    
    Same as purescript_binary but with test runner integration.
    """
    # Reuse binary implementation
    providers = _purescript_binary_impl(ctx)
    
    # Add test runner info if needed
    return providers

purescript_test = rule(
    impl = _purescript_test_impl,
    attrs = {
        "srcs": attrs.list(attrs.source(), default = [], doc = "PureScript test source files (.purs)"),
        "deps": attrs.list(attrs.dep(), default = [], doc = "PureScript library dependencies"),
        "main": attrs.option(attrs.string(), default = None, doc = "Test main module (default: Test.Main)"),
        "purs_flags": attrs.list(attrs.string(), default = [], doc = "Additional purs compiler flags"),
    },
)

# ═══════════════════════════════════════════════════════════════════════════════
# PURESCRIPT TOOLCHAIN RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _purescript_toolchain_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    PureScript toolchain with paths from .buckconfig.local.
    
    Reads [purescript] section for:
      purs    - PureScript compiler
      spago   - Package manager
      node    - Node.js runtime
      esbuild - JavaScript bundler
    """
    purs = read_root_config("purescript", "purs", ctx.attrs.purs)
    spago = read_root_config("purescript", "spago", ctx.attrs.spago)
    node = read_root_config("purescript", "node", ctx.attrs.node)
    esbuild = read_root_config("purescript", "esbuild", ctx.attrs.esbuild)
    
    return [
        DefaultInfo(),
        PurescriptToolchainInfo(
            purs = purs,
            spago = spago,
            node = node,
            esbuild = esbuild,
        ),
    ]

purescript_toolchain = rule(
    impl = _purescript_toolchain_impl,
    attrs = {
        "purs": attrs.string(default = "purs", doc = "Path to purs compiler"),
        "spago": attrs.option(attrs.string(), default = None, doc = "Path to spago"),
        "node": attrs.string(default = "node", doc = "Path to node"),
        "esbuild": attrs.option(attrs.string(), default = None, doc = "Path to esbuild"),
    },
    is_toolchain_rule = True,
)
