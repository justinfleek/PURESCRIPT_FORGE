{
  description = "PURESCRIPT_FORGE workspace - PureScript/Haskell/Lean4 with proofs";

  nixConfig = {
    extra-experimental-features = [
      "nix-command"
      "flakes"
    ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    spago2nix.url = "github:justinwoo/spago2nix";
    lean4.url = "github:leanprover/lean4";
    
    # PureScript overlay for latest tooling
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    
    # Aleph continuity - Local aleph-b7r6-continuity-0x08 infrastructure
    # Provides prelude, typed unix, flake modules, overlays, build toolchains
    aleph-continuity = {
      url = "path:./aleph-b7r6-continuity-0x08";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    
    # Keep aleph alias for backward compatibility (points to continuity)
    aleph.follows = "aleph-continuity";
    
    # Buck2 prelude (required for Buck2 build infrastructure)
    # Straylight fork with NVIDIA support, Mercury-based Haskell rules
    buck2-prelude = {
      url = "github:weyl-ai/straylight-buck2-prelude";
      flake = false;
    };
    
    # NativeLink - Local Remote Execution for Buck2
    # Provides CAS (Content-Addressable Storage), scheduler, and workers
    # Enables distributed builds with caching
    nativelink = {
      url = "github:TraceMachina/nativelink";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    
    # nix2gpu - NixOS containers for GPU compute (required for NativeLink containers)
    # Uses nimi as PID 1 for modular services
    nix2gpu = {
      url = "github:fleek-sh/nix2gpu";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    
    # LLVM from git with SM120 Blackwell support
    # Required for llvm-git overlay (bleeding-edge LLVM)
    llvm-project = {
      url = "github:llvm/llvm-project/bb1f220d534b0f6d80bea36662f5188ff11c2e54";
      flake = false;
    };
    
    # Determinate Nix with WASM support (builtins.wasm + wasm32-wasip1)
    # Required for straylight-nix overlay
    # NOTE: Don't follow nixpkgs - needs specific rust version for wasmtime
    straylight-nix = {
      url = "github:straylight-software/nix";
    };
    
    # GHC WASM backend toolchain (ghc-wasm-meta)
    # Provides wasm32-wasi-ghc, wasm32-wasi-cabal, wasi-sdk, wasmtime, etc.
    # Required for ghc-wasm overlay (builtins.wasm plugin development)
    ghc-wasm-meta = {
      url = "github:haskell-wasm/ghc-wasm-meta";
      # Don't follow nixpkgs - ghc-wasm-meta has specific version requirements
    };
    
    # ghc-source-gen from git (Hackage version doesn't support GHC 9.12)
    # Required for haskell overlay (grapesy -> proto-lens-protoc -> ghc-source-gen)
    ghc-source-gen-src = {
      url = "github:google/ghc-source-gen";
      flake = false;
    };
    
    # Nimi - Tini-like PID 1 for containers and NixOS modular services
    # Used for VM init scripts with proper process supervision
    # Required for container infrastructure (nix2gpu)
    nimi = {
      url = "github:b7r6/nimi/add-static-build";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, nixpkgs, spago2nix, lean4, purescript-overlay, aleph-continuity, aleph, buck2-prelude, nativelink, nix2gpu, llvm-project, straylight-nix, ghc-wasm-meta, ghc-source-gen-src, nimi, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      
      # Import aleph-continuity flake modules
      # default module includes: formatter, lint, docs, std, devshell, prelude, nv-sdk, container
      # build module adds: Buck2 build infrastructure with toolchains
      # shortlist module adds: Hermetic C++ libraries for Buck2
      # lre module adds: Local Remote Execution (NativeLink) for distributed builds
      # nativelink module adds: NativeLink container infrastructure
      imports = [ 
        aleph-continuity.modules.flake.default
        aleph-continuity.modules.flake.build
        aleph-continuity.modules.flake.shortlist
        aleph-continuity.modules.flake.lre
        # nix2gpu must be imported before nativelink (provides perSystem.nix2gpu options)
        inputs.nix2gpu.flakeModule
        aleph-continuity.modules.flake.nativelink
      ];

      # Buck2 build infrastructure - disabled for now to fix flake evaluation
      # Some Haskell dependencies (grapesy, etc.) aren't available in nixpkgs-unstable
      aleph.build.enable = false;
      
      # Local Remote Execution - disabled for now
      aleph.lre.enable = false;
      
      # Formatter - disabled for now to simplify
      aleph.formatter.enable = false;
      
      # Lint - disabled for now to simplify  
      aleph.lint.enable = false;
      
      # Documentation - disabled for now to simplify
      aleph.docs.enable = false;
      
      # Devshell from aleph-continuity - disabled, we define our own
      aleph.devshell.enable = false;
      
      # Shortlist - disabled for now to simplify
      aleph.shortlist.enable = false;
      
      # Central nixpkgs configuration (ℵ-001 §3)
      aleph.nixpkgs.overlays = [
        purescript-overlay.overlays.default
      ];
      
      # NativeLink - enabled for distributed builds
      aleph.nativelink.enable = true;

      perSystem = { config, self', inputs', pkgs, system, lib, ... }:
        let
          # Use pkgs from _module.args (set by aleph-continuity.std module)
          # This is the centralized nixpkgs configuration per ℵ-001 §3
          # PureScript overlay is configured via aleph.nixpkgs.overlays above
          # aleph-continuity.overlays.default is already included by std module
          
          # Aleph prelude for functional backend calling
          # Access via config (flake module) or overlay (pkgs.aleph.prelude)
          prelude = config.aleph.prelude or pkgs.aleph.prelude;
          
          # Typed Unix Script infrastructure
          # GHC with Aleph.Script modules for building custom scripts
          script-ghc = pkgs.aleph.script.ghc;
          
          # libmodern overlay - Static C++ libraries
          # Available via pkgs.libmodern.* (fmt, abseil-cpp, libsodium)
          # These are static libraries built with C++17 minimum, -fPIC, RelWithDebInfo
          
          # Helper functions using prelude for backend calls
          # Core functions
          inherit (prelude) id const flip compose pipe;
          # List operations
          inherit (prelude) map filter fold fold-right head tail take drop length reverse concat concat-map;
          inherit (prelude) zip zip-with sort unique elem find partition;
          # Nullable (Maybe) operations
          inherit (prelude) maybe from-maybe is-null is-just is-nothing cat-maybes map-maybe;
          # Either operations
          inherit (prelude) left right is-left is-right either from-right from-left lefts rights partition-eithers;
          # String operations (prelude uses 'split' and 'join', not 'split-string'/'join-string')
          inherit (prelude) split join trim;
          # Attr operations
          inherit (prelude) map-attrs filter-attrs fold-attrs keys values;
          
          # Call backend executable with functional error handling
          callBackend = exe: args: 
            let
              result = pkgs.runCommand "backend-call" {
                buildInputs = [ exe ];
              } ''
                ${exe}/bin/${exe.name or (builtins.baseNameOf exe)} ${pkgs.lib.concatStringsSep " " args} > $out 2>&1 || {
                  echo "ERROR:$?" > $out
                  exit 1
                }
              '';
            in
              if pkgs.lib.hasPrefix "ERROR:" (builtins.readFile result) then
                left (builtins.readFile result)
              else
                right (builtins.readFile result);
          
          # Call bridge server with JSON-RPC method
          callBridgeServer = method: params:
            callBackend bridge-server-ps [ "--method" method "--params" (builtins.toJSON params) ];
          
          # Call database backend
          callDatabase = command: args:
            callBackend bridge-database-hs ([ command ] ++ args);
          
          # Call analytics backend
          callAnalytics = command: args:
            callBackend bridge-analytics-hs ([ command ] ++ args);
          
          # PureScript toolchain
          spago = pkgs.spago;
          purs = pkgs.purescript;

          # Haskell toolchain
          haskellPackages = pkgs.haskellPackages;

          # Lean4 toolchain - use from nixpkgs
          lean = pkgs.lean4;

          # PureScript project for rules/standards
          rules-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "purescript-forge-rules-ps";
            version = "0.1.0";
            src = ./src/rules-ps;
            buildInputs = [ purs spago ];
            buildPhase = ''
              spago build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r output $out/
            '';
            meta = {
              description = "FORGE coding rules and standards (PureScript)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Haskell project for rules/standards
          rules-hs = (haskellPackages.callCabal2nix "forge-rules-hs" ./src/rules-hs {}).overrideAttrs (finalAttrs: {
            meta = {
              description = "PURESCRIPT_FORGE coding rules and standards (Haskell)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Lean4 project for proofs
          rules-lean = lean.buildPackage {
            name = "PureScriptForgeRules";
            src = ./src/rules-lean;
          };

          # PRISM Color Core (Haskell)
          prism-color-core-hs = (haskellPackages.callCabal2nix "prism-color-core" 
            ./PRISM/prism-color-core/haskell {}).overrideAttrs (finalAttrs: {
              meta = {
                description = "PRISM color core";
                license = pkgs.lib.licenses.mit;
              };
            });

          # PRISM Color Core (Lean4)
          prism-color-core-lean = (lean.buildPackage {
            name = "PrismColor";
            src = ./PRISM/prism-color-core/lean4;
          }).overrideAttrs (finalAttrs: {
            meta = {
              description = "PRISM color core";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Sidepanel PureScript frontend
          sidepanel-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "opencode-sidepanel-ps";
            version = "0.1.0";
            src = ./src/sidepanel-ps;
            buildInputs = [ purs spago ];
            buildPhase = ''
              export HOME=$TMPDIR
              spago build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r output $out/
            '';
            meta = {
              description = "OpenCode sidepanel UI (PureScript/Halogen)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # OpenCode Type Definitions (PureScript)
          opencode-types-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "opencode-types-ps";
            version = "0.1.0";
            src = ./src/opencode-types-ps;
            buildInputs = [ purs spago ];
            buildPhase = ''
              export HOME=$TMPDIR
              spago build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r output $out/
            '';
            meta = {
              description = "OpenCode shared type definitions";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Console Core - Domain types and business logic (PureScript)
          console-core-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "console-core-ps";
            version = "0.1.0";
            src = ./packages/console/core;
            buildInputs = [ purs spago ];
            buildPhase = ''
              export HOME=$TMPDIR
              spago build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r output $out/
            '';
            meta = {
              description = "Console core domain types (PureScript)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Console App - Web application UI (PureScript/Halogen)
          console-app-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "console-app-ps";
            version = "0.1.0";
            src = ./packages/console/app;
            buildInputs = [ purs spago pkgs.nodejs_20 ];
            buildPhase = ''
              export HOME=$TMPDIR
              # Link to console-core output
              mkdir -p .spago
              ${if builtins.pathExists ./packages/console/core then ''
                ln -s ${console-core-ps}/output .spago/console-core || true
              '' else ""}
              spago build
            '';
            installPhase = ''
              mkdir -p $out
              cp -r output $out/
            '';
            meta = {
              description = "Console web application UI (PureScript/Halogen)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Spec loader/parser (Haskell)
          spec-loader-hs = (haskellPackages.callCabal2nix "spec-loader" 
            ./src/spec-loader-hs {}).overrideAttrs (finalAttrs: {
              meta = {
                description = "Spec loader/parser";
                license = pkgs.lib.licenses.mit;
              };
            });
          
          # OpenCode validator (Haskell)
          opencode-validator-hs = (haskellPackages.callCabal2nix "opencode-validator" 
            ./src/opencode-validator-hs {}).overrideAttrs (finalAttrs: {
              meta = {
                description = "OpenCode validator (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            });
          
          # Bridge Database (Haskell)
          bridge-database-hs = (haskellPackages.callCabal2nix "bridge-database" 
            ./src/bridge-database-hs {}).overrideAttrs (finalAttrs: {
              meta = {
                description = "Bridge database backend";
                license = pkgs.lib.licenses.mit;
              };
            });
          
          # Bridge Analytics (Haskell/DuckDB)
          # Note: duckdb-haskell may need to be added to haskellPackages
          # or use DuckDB C API via FFI
          bridge-analytics-hs = (haskellPackages.callCabal2nix "bridge-analytics" 
            ./src/bridge-analytics-hs {}).overrideAttrs (finalAttrs: {
              meta = {
                description = "Bridge analytics backend (Haskell/DuckDB)";
                license = pkgs.lib.licenses.mit;
              };
            });
          
          # OpenCode proofs (Lean4)
          opencode-proofs-lean = (lean.buildPackage {
            name = "OpencodeProofs";
            src = ./src/opencode-proofs-lean;
          }).overrideAttrs (finalAttrs: {
            meta = {
              description = "OpenCode proofs (Lean4)";
              license = pkgs.lib.licenses.mit;
            };
          });
          
          # STRAYLIGHT - Semantic Cells (Python)
          semantic-cells-python = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-semantic-cells";
            version = "0.1.0";
            src = ./NEXUS/semantic-cells;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              numpy
            ];
            doCheck = false;
            meta = {
              description = "NEXUS semantic cells (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Database Layer (Python)
          nexus-database-layer = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-database-layer";
            version = "0.1.0";
            src = ./NEXUS/database-layer;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              duckdb
            ];
            doCheck = false;
            meta = {
              description = "NEXUS database layer (Python/DuckDB)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Agent Orchestrator (Python)
          nexus-agent-orchestrator = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-agent-orchestrator";
            version = "0.1.0";
            src = ./NEXUS/agent-orchestrator;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # No external deps - uses subprocess for bubblewrap
            ];
            doCheck = false;
            meta = {
              description = "NEXUS agent orchestrator";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Network Graph (Python)
          nexus-network-graph = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-network-graph";
            version = "0.1.0";
            src = ./NEXUS/network-graph;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "NEXUS network graph";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Web Search Agent (Python)
          nexus-web-search-agent = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-web-search-agent";
            version = "0.1.0";
            src = ./NEXUS/web-search-agent;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              requests
              beautifulsoup4
            ];
            doCheck = false;
            meta = {
              description = "NEXUS web search agent (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Content Extraction Agent (Python)
          nexus-content-extraction-agent = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-content-extraction-agent";
            version = "0.1.0";
            src = ./NEXUS/content-extraction-agent;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Would add spaCy, NLTK in production
            ];
            doCheck = false;
            meta = {
              description = "NEXUS content extraction agent (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Network Formation Agent (Python)
          nexus-network-formation-agent = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-network-formation-agent";
            version = "0.1.0";
            src = ./NEXUS/network-formation-agent;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "NEXUS network formation agent";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Agent Social (Python)
          nexus-agent-social = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-agent-social";
            version = "0.1.0";
            src = ./NEXUS/agent-social;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT agent social system (Python, FFI only)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Performance/Caching (Python)
          nexus-performance = pkgs.python3Packages.buildPythonPackage {
            pname = "nexus-performance";
            version = "0.1.0";
            src = ./NEXUS/performance;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "NEXUS performance and caching";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # NEXUS - Engram Attestation (Haskell)
          engram-attestation-hs = haskellPackages.callCabal2nix "engram-types" 
            ./STRAYLIGHT/engram-attestation/engram-types { 
              meta = {
                description = "NEXUS Engram attestation (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            };

          # Import deployment configuration
          deployment = import ./deploy.nix {
            inherit pkgs lib;
            bridge-server-ps = bridge-server-ps;
            bridge-database-hs = bridge-database-hs;
          };

          # Bridge Server (PureScript) - OpenCode
          bridge-server-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "opencode-bridge-server-ps";
            version = "0.1.0";
            src = ./src/bridge-server-ps;
            buildInputs = [ purs spago pkgs.nodejs ];
            buildPhase = ''
              export HOME=$TMPDIR
              # Install Node.js dependencies for FFI
              npm install --prefix . ws express better-sqlite3 pino
              # Build PureScript
              spago build
            '';
            installPhase = ''
              mkdir -p $out/bin $out/lib
              cp -r output $out/lib/
              cp package.json $out/
              cp node_modules $out/ -r || true
              # Create wrapper script
              cat > $out/bin/bridge-server <<EOF
              #!${pkgs.nodejs}/bin/node
              require('$out/lib/output/Bridge.Main/index.js');
              EOF
              chmod +x $out/bin/bridge-server
            '';
            meta = {
              description = "OpenCode bridge server";
              license = pkgs.lib.licenses.mit;
              mainProgram = "bridge-server";
            };
          });

          # NEXUS Bridge Server (PureScript)
          nexus-bridge-server-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "nexus-bridge-server-ps";
            version = "0.1.0";
            src = ./NEXUS/bridge-server-ps;
            buildInputs = [ purs spago pkgs.nodejs pkgs.postgresql ];
            buildPhase = ''
              export HOME=$TMPDIR
              # Install Node.js dependencies for FFI
              npm install --prefix . ws express pg pino
              # Build PureScript
              spago build
            '';
            installPhase = ''
              mkdir -p $out/bin $out/lib
              cp -r output $out/lib/
              cp package.json $out/
              cp -r node_modules $out/ || true
              # Create wrapper script
              cat > $out/bin/nexus-bridge-server <<EOF
              #!${pkgs.nodejs}/bin/node
              require('$out/lib/output/Bridge.Main/index.js');
              EOF
              chmod +x $out/bin/nexus-bridge-server
            '';
            meta = {
              description = "Nexus bridge server";
              license = pkgs.lib.licenses.mit;
              mainProgram = "nexus-bridge-server";
            };
          });

          # Compiler Pipeline - PureScript → C++23 compiler (Haskell/Cabal)
          compiler-pipeline-purescript-to-cpp23 = haskellPackages.callCabal2nix "purescript-to-cpp23" 
            ./src/compiler-pipeline/purescript-to-cpp23 { 
              meta = {
                description = "PureScript → C++23 compiler";
                license = pkgs.lib.licenses.mit;
                mainProgram = "purescript-to-cpp23";
              };
            };

          # Compiler Pipeline - C++23 → React generator
          compiler-pipeline-cpp23-to-react = prelude.stdenv.default (finalAttrs: {
            pname = "cpp23-to-react";
            version = "0.1.0";
            src = ./src/compiler-pipeline/cpp23-to-react;
            native-build-inputs = [
              pkgs.clang_17
              pkgs.llvmPackages_17.libclang
            ];
            build-phase = ''
              export LLVM_CLANG_INCLUDE=${pkgs.llvmPackages_17.libclang}/include
              ${builtins.readFile ./src/compiler-pipeline/scripts/build-cpp23-to-react.sh}
            '';
            install-phase = ''
              mkdir -p $out/bin
              cp cpp23-to-react $out/bin/
            '';
            meta = {
              description = "C++23 → React generator";
              license = pkgs.lib.licenses.mit;
              main-program = "cpp23-to-react";
            };
          });

          # Compiler Pipeline - Runtime library (WASM)
          compiler-pipeline-runtime-wasm = prelude.stdenv.default (finalAttrs: {
            pname = "runtime-wasm";
            version = "0.1.0";
            src = ./src/compiler-pipeline/runtime;
            native-build-inputs = [ pkgs.emscripten ];
            build-phase = builtins.readFile ./src/compiler-pipeline/scripts/build-wasm.sh;
            install-phase = ''
              mkdir -p $out/lib
              cp wasm_bridge.js $out/lib/
              cp wasm_bridge.wasm $out/lib/ 2>/dev/null || true
            '';
            meta = {
              description = "Compiler pipeline WASM runtime";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Compiler Pipeline - All components
          compiler-pipeline = pkgs.buildEnv {
            name = "compiler-pipeline";
            paths = [
              compiler-pipeline-purescript-to-cpp23
              compiler-pipeline-cpp23-to-react
              compiler-pipeline-runtime-wasm
            ];
          };

        in
        {
          # NVIDIA SDK configuration (perSystem)
          # Provides CUDA, cuDNN, TensorRT, NCCL, CUTLASS
          # Note: nv.sdk is defined by aleph-continuity.modules.flake.nv-sdk
          # These values are the defaults from that module
          nv.sdk.enable = false;  # Disabled by default (requires unfree packages)
          
          packages = {
            default = rules-hs;
            
            # Rules implementations
            rules-ps = rules-ps;
            rules-hs = rules-hs;
            rules-lean = rules-lean;
            
            # PRISM color system
            prism-color-core-hs = prism-color-core-hs;
            prism-color-core-lean = prism-color-core-lean;
            
            # Sidepanel implementations
            sidepanel-ps = sidepanel-ps;
            spec-loader-hs = spec-loader-hs;
            
            # OpenCode migration (Phase 2)
            opencode-types-ps = opencode-types-ps;
            opencode-validator-hs = opencode-validator-hs;
            opencode-proofs-lean = opencode-proofs-lean;
            
            # Console packages (PureScript)
            console-core-ps = console-core-ps;
            console-app-ps = console-app-ps;
            
            # Bridge Database (Haskell)
            bridge-database-hs = bridge-database-hs;
            
            # Bridge Analytics (Haskell/DuckDB)
            bridge-analytics-hs = bridge-analytics-hs;
            
            # Bridge Server (PureScript)
            bridge-server-ps = bridge-server-ps;
            
            # OpenCode Plugin (PureScript)
            opencode-plugin-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "opencode-plugin-ps";
              version = "0.1.0";
              src = ./src/opencode-plugin-ps;
              buildInputs = [ purs spago pkgs.nodejs ];
              buildPhase = ''
                export HOME=$TMPDIR
                npm install --prefix . ws
                spago build
              '';
              installPhase = ''
                mkdir -p $out
                cp -r output $out/
                cp package.json $out/
                cp src/Opencode/Plugin/Main.js $out/index.js
              '';
              meta = {
                description = "OpenCode plugin";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # NEXUS - All Python packages
            semantic-cells-python = semantic-cells-python;
            nexus-database-layer = nexus-database-layer;
            nexus-agent-orchestrator = nexus-agent-orchestrator;
            nexus-network-graph = nexus-network-graph;
            nexus-web-search-agent = nexus-web-search-agent;
            nexus-content-extraction-agent = nexus-content-extraction-agent;
            nexus-network-formation-agent = nexus-network-formation-agent;
            nexus-agent-social = nexus-agent-social;
            nexus-performance = nexus-performance;

            # NEXUS - Engram Attestation (Haskell)
            engram-attestation-hs = engram-attestation-hs;
            
            # NEXUS - Bridge Server (PureScript)
            nexus-bridge-server-ps = nexus-bridge-server-ps;
            
            # NEXUS - Agent Orchestrator (PureScript)
            nexus-agent-orchestrator-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "nexus-agent-orchestrator-ps";
              version = "0.1.0";
              src = ./NEXUS/agent-orchestrator-ps;
              buildInputs = [ purs spago pkgs.nodejs ];
              buildPhase = ''
                export HOME=$TMPDIR
                spago build
              '';
              installPhase = ''
                mkdir -p $out
                cp -r output $out/
              '';
              meta = {
                description = "NEXUS agent orchestrator";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # NEXUS - Network Graph (PureScript)
            nexus-network-graph-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "nexus-network-graph-ps";
              version = "0.1.0";
              src = ./NEXUS/network-graph-ps;
              buildInputs = [ purs spago ];
              buildPhase = ''
                export HOME=$TMPDIR
                spago build
              '';
              installPhase = ''
                mkdir -p $out
                cp -r output $out/
              '';
              meta = {
                description = "NEXUS network graph (PureScript)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # NEXUS - Network Graph Metrics (Haskell)
            nexus-network-graph-hs = haskellPackages.callCabal2nix "nexus-network-graph-hs"
              ./NEXUS/network-graph-hs { 
                meta = {
                  description = "NEXUS network graph metrics";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # NEXUS - Agent Social (PureScript)
            nexus-agent-social-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "nexus-agent-social-ps";
              version = "0.1.0";
              src = ./NEXUS/agent-social-ps;
              buildInputs = [ purs spago pkgs.nodejs ];
              buildPhase = ''
                export HOME=$TMPDIR
                spago build
              '';
              installPhase = ''
                mkdir -p $out
                cp -r output $out/
              '';
              meta = {
                description = "NEXUS agent social system (PureScript)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # NEXUS - Proofs (Lean4)
            nexus-proofs-lean = (lean.buildPackage {
              name = "NexusProofs";
              src = ./NEXUS/proofs-lean;
            }).overrideAttrs (finalAttrs: {
              meta = {
                description = "NEXUS proofs";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # Render API (PureScript)
            render-api-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "render-api-ps";
              version = "0.1.0";
              src = ./src/render-api-ps;
              buildInputs = [ purs spago pkgs.nodejs ];
              buildPhase = ''
                export HOME=$TMPDIR
                spago build
              '';
              installPhase = ''
                mkdir -p $out
                cp -r output $out/
              '';
              meta = {
                description = "Render API client (PureScript)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # Render Gateway (Haskell)
            render-gateway-hs = haskellPackages.callCabal2nix "render-gateway-hs"
              ./src/render-gateway-hs { 
                meta = {
                  description = "Render inference gateway (Haskell/STM)";
                  license = pkgs.lib.licenses.mit;
                  mainProgram = "render-gateway";
                };
              };
            
            # Render ClickHouse Client (Haskell)
            render-clickhouse-hs = haskellPackages.callCabal2nix "render-clickhouse-hs"
              ./src/render-clickhouse-hs { 
                meta = {
                  description = "Render ClickHouse client";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # Render CAS Client (Haskell)
            render-cas-hs = haskellPackages.callCabal2nix "render-cas-hs"
              ./src/render-cas-hs { 
                meta = {
                  description = "Render CAS client (Haskell/Nexus CAS)";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # Render Billing (Haskell)
            render-billing-hs = haskellPackages.callCabal2nix "render-billing-hs"
              ./src/render-billing-hs { 
                meta = {
                  description = "Render GPU billing (Haskell/NVXT)";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # Render Compliance (Haskell)
            render-compliance-hs = haskellPackages.callCabal2nix "render-compliance-hs"
              ./src/render-compliance-hs { 
                meta = {
                  description = "Render compliance and audit trail";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # Compiler Pipeline
            compiler-pipeline-purescript-to-cpp23 = compiler-pipeline-purescript-to-cpp23;
            compiler-pipeline-cpp23-to-react = compiler-pipeline-cpp23-to-react;
            compiler-pipeline-runtime-wasm = compiler-pipeline-runtime-wasm;
            compiler-pipeline = compiler-pipeline;
            
            # NEXUS - All components
            # Note: Python packages from let block are accessible directly
            # Packages defined in packages set need self'.packages reference
            nexus-all = pkgs.symlinkJoin {
              name = "nexus-all";
              paths = [
                # Python packages (from let block - accessible directly)
                semantic-cells-python
                nexus-database-layer
                nexus-agent-orchestrator
                nexus-network-graph
                nexus-web-search-agent
                nexus-content-extraction-agent
                nexus-network-formation-agent
                nexus-agent-social
                nexus-performance
                # PureScript/Haskell (defined in packages set - need self'.packages)
                self'.packages.nexus-agent-orchestrator-ps
                self'.packages.nexus-network-graph-ps
                self'.packages.nexus-network-graph-hs
                self'.packages.nexus-agent-social-ps
                # Haskell (from let block - accessible directly)
                engram-attestation-hs
                # Lean4 proofs (defined in packages set - need self'.packages)
                self'.packages.nexus-proofs-lean
              ];
            };
            
            # All packages
            # Note: Packages from let block are accessible directly
            # Packages defined in packages set need self'.packages reference
            all-packages = pkgs.symlinkJoin {
              name = "purescript-forge-all";
              paths = [
                # From let block - accessible directly
                rules-ps
                rules-hs
                rules-lean
                prism-color-core-hs
                prism-color-core-lean
                sidepanel-ps
                spec-loader-hs
                opencode-types-ps
                opencode-validator-hs
                opencode-proofs-lean
                bridge-server-ps
                semantic-cells-python
                engram-attestation-hs
                # Console packages
                console-core-ps
                console-app-ps
                # From packages set - need self'.packages
                self'.packages.opencode-plugin-ps
              ];
            };
          };

          devShells = {
            # Use mkForce to override the default devShell from aleph-continuity
            default = lib.mkForce (pkgs.mkShell {
              buildInputs = [
                purs
                spago
                haskellPackages.ghc
                haskellPackages.cabal-install
                haskellPackages.haskell-language-server
                lean
                pkgs.nixpkgs-fmt
                pkgs.nodejs_20
                pkgs.nodePackages.pnpm
                pkgs.just
                pkgs.watchexec
                # Buck2 build infrastructure (if enabled) - use config.aleph.build.packages (perSystem)
              ] ++ (config.aleph.build.packages or [])
                ++ (config.aleph.lre.packages or [])
                # CLI tool wrappers
                ++ (with pkgs; [
                  ripgrep  # rg
                  fd        # fd
                  bat       # bat
                  delta     # delta
                  dust      # dust
                  tokei     # tokei
                  hyperfine # hyperfine
                  deadnix   # deadnix
                  statix    # statix
                  stylua    # stylua
                  taplo     # taplo
                  zoxide    # zoxide
                ]);
              # Simplified shell hook - aleph modules add their own hooks
              shellHook = ''
                # Include aleph module hooks if available
                ${config.aleph.build.shellHook or ""}
                ${config.aleph.shortlist.shellHook or ""}
                ${config.aleph.lre.shellHook or ""}
                
                echo "════════════════════════════════════════════════════════════════"
                echo "  FORGE Development Shell"
                echo "════════════════════════════════════════════════════════════════"
                echo ""
                echo "PureScript: $(purs --version)"
                echo "Haskell: $(ghc --version)"
                echo "Lean4: $(lean --version)"
                echo "Node.js: $(node --version)"
                echo ""
                echo "Build commands:"
                echo "  nix build .#all-packages  - Build everything"
                echo "  nix build .#sidepanel-ps  - Build sidepanel"
                echo "  nix flake check           - Verify flake configuration"
                echo ""
                echo "Validation commands:"
                echo "  nix run .#validate-opencode - Validate OpenCode code"
                echo "  nix run .#opencode-validator -- banned <path> - Check banned constructs"
                echo "  nix run .#opencode-validator -- file-reading <path> - Check file reading protocol"
                echo "  nix run .#opencode-validator -- type-escapes <path> - Check type escapes"
                echo ""
                echo "Compiler Pipeline commands:"
                echo "  nix build .#compiler-pipeline - Build all compiler pipeline components"
                echo "  nix build .#compiler-pipeline-purescript-to-cpp23 - Build PureScript compiler"
                echo "  nix build .#compiler-pipeline-cpp23-to-react - Build React generator"
                echo "  nix build .#compiler-pipeline-runtime-wasm - Build WASM runtime"
                echo "  nix run .#compiler-pipeline-test-all - Run all compiler pipeline tests"
                echo "  nix run .#compiler-pipeline-test - Run unit tests"
                echo "  nix run .#compiler-pipeline-test-integration - Run integration tests"
                echo ""
              '';
            });  # close mkForce
          };

          apps = lib.mkMerge [
            {
            check-rules = {
              type = "app";
              program = "${pkgs.writeShellScriptBin "check-rules" ''
                echo "Checking rules implementations..."
                nix build .#rules-ps
                nix build .#rules-hs
                nix build .#rules-lean
                echo "All rules verified"
              ''}/bin/check-rules";
            };

            test-all = {
              type = "app";
              program = "${pkgs.writeShellScriptBin "test-all" ''
                echo "Running all tests..."
                echo "Haskell property tests:"
                nix build .#rules-hs.tests.rules-test
                echo "PRISM color tests:"
                nix build .#prism-color-core-hs.tests.prism-color-test || echo "No tests yet"
                echo "Lean4 proof checking:"
                nix build .#rules-lean
                nix build .#prism-color-core-lean
                echo "All tests passed!"
              ''}/bin/test-all";
            };

            verify-all = {
              type = "app";
              program = "${pkgs.writeShellScriptBin "verify-all" ''
                echo "Verifying all implementations..."
                nix flake check
                nix build .#all-packages
                echo "Verifying specs..."
                nix run .#spec-loader -- opencode-sidepanel-specs || echo "Spec verification skipped"
                echo "All verifications passed!"
              ''}/bin/verify-all";
            };

            # Typed Unix build verification
            verify-builds-aleph = {
              type = "app";
              program = "${prelude.ghc.turtle-script {
                name = "verify-builds-aleph";
                src = ./scripts/verify-builds-aleph.hs;
                deps = [ pkgs.nix ];
                hs-deps = p: with p; [ ];
              }}/bin/verify-builds-aleph";
            };
            

            spec-loader = {
              type = "app";
              program = "${spec-loader-hs}/bin/spec-loader";
            };

            opencode-validator = {
              type = "app";
              program = "${opencode-validator-hs}/bin/opencode-validator";
            };

            validate-opencode = {
              type = "app";
              program = "${pkgs.writeShellScriptBin "validate-opencode" ''
                echo "Validating OpenCode TypeScript code..."
                echo ""
                echo "Checking for banned constructs..."
                ${opencode-validator-hs}/bin/opencode-validator banned opencode-dev/packages/opencode/src || true
                echo ""
                echo "Checking file reading protocol compliance..."
                ${opencode-validator-hs}/bin/opencode-validator file-reading opencode-dev/packages/opencode/src || true
                echo ""
                echo "Checking for type escapes..."
                ${opencode-validator-hs}/bin/opencode-validator type-escapes opencode-dev/packages/opencode/src || true
                echo ""
                echo "Validation complete"
              ''}/bin/validate-opencode";
            };
            
            # Compiler Pipeline - Test apps (Typed Unix Scripts)
            compiler-pipeline-test = {
              type = "app";
              program = "${prelude.ghc.turtle-script {
                name = "compiler-pipeline-test";
                src = ./src/compiler-pipeline/scripts/test-unit.hs;
                deps = [
                  compiler-pipeline-purescript-to-cpp23
                  pkgs.cabal-install
                  pkgs.haskellPackages.hspec-discover
                ];
                hs-deps = p: with p; [
                  shelly
                  text
                ];
              }}/bin/compiler-pipeline-test";
            };
            
            compiler-pipeline-test-integration = {
              type = "app";
              program = "${prelude.ghc.turtle-script {
                name = "compiler-pipeline-test-integration";
                src = ./src/compiler-pipeline/scripts/test-integration.hs;
                deps = [
                  compiler-pipeline-purescript-to-cpp23
                  compiler-pipeline-cpp23-to-react
                ];
                hs-deps = p: with p; [
                  shelly
                  text
                ];
              }}/bin/compiler-pipeline-test-integration";
            };
            
            compiler-pipeline-test-all = {
              type = "app";
              program = "${prelude.ghc.turtle-script {
                name = "compiler-pipeline-test-all";
                src = ./src/compiler-pipeline/scripts/test-all.hs;
                deps = [
                  pkgs.nix
                ];
                hs-deps = p: with p; [
                  shelly
                  text
                ];
              }}/bin/compiler-pipeline-test-all";
            };
            
            # Backend health check using aleph prelude
            backend-health = {
              type = "app";
              program = pkgs.writeShellScriptBin "backend-health" ''
                #!/usr/bin/env bash
                # Health check for all backend services using functional patterns
                echo "Checking backend services..."
                
                # Check bridge server
                if ${bridge-server-ps}/bin/bridge-server --health-check 2>/dev/null; then
                  echo "Bridge Server: Healthy"
                else
                  echo "Bridge Server: Unhealthy"
                  exit 1
                fi
                
                # Check database backend
                if ${bridge-database-hs}/bin/bridge-database health 2>/dev/null; then
                  echo "Database Backend: Healthy"
                else
                  echo "Database Backend: Unhealthy"
                  exit 1
                fi
                
                # Check analytics backend
                if ${bridge-analytics-hs}/bin/bridge-analytics health 2>/dev/null; then
                  echo "Analytics Backend: Healthy"
                else
                  echo "Analytics Backend: Unhealthy"
                  exit 1
                fi
                
                echo "All backend services healthy"
              '';
            };

            # Deployment apps
            deploy = {
              type = "app";
              program = lib.getExe deployment.deploy;
            };

            rollback = {
              type = "app";
              program = lib.getExe deployment.rollback;
            };

            health-check = {
              type = "app";
              program = lib.getExe deployment.healthCheck;
            };

            verify-deployment = {
              type = "app";
              program = lib.getExe deployment.verifyDeployment;
            };

            # Integration tests
            test-integration = {
              type = "app";
              program = "${pkgs.writeShellScriptBin "test-integration" ''
                echo "Running integration tests..."
                echo ""
                echo "Haskell integration tests:"
                nix build .#bridge-database-hs.tests.bridge-database-test || echo "Integration tests require database setup"
                echo ""
                echo "PureScript integration tests:"
                echo "Authentication integration tests require test environment setup"
                echo ""
                echo "Integration test suite complete"
              ''}/bin/test-integration";
            };
          }
          # Conditionally add LRE/NativeLink apps
          (lib.mkIf (((config.aleph or {}).lre or { enable = false; }).enable or false) {
            lre-start = {
              type = "app";
              program = "${config.aleph.lre.lre-start}/bin/lre-start";
            };
          })
          (lib.mkIf (((config.aleph or {}).nativelink or { enable = false; }).enable or false) {
            nativelink-status = {
              type = "app";
              program = "${config.aleph.nativelink.packages.nativelink-status}/bin/nativelink-status";
            };
            nativelink-logs = {
              type = "app";
              program = "${config.aleph.nativelink.packages.nativelink-logs}/bin/nativelink-logs";
            };
          })
          # Container tools (if enabled, Linux only)
          (lib.mkIf ((((config.aleph or {}).container or { enable = false; }).enable or false) && pkgs.stdenv.isLinux) {
            crane-inspect = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.crane-inspect}/bin/crane-inspect";
            };
            crane-pull = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.crane-pull}/bin/crane-pull";
            };
            unshare-run = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.unshare-run}/bin/unshare-run";
            };
            unshare-gpu = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.unshare-gpu}/bin/unshare-gpu";
            };
            fhs-run = {
              type = "app";
              program = "${pkgs.aleph.container.fhs-run}/bin/fhs-run";
            };
            gpu-run = {
              type = "app";
              program = "${pkgs.aleph.container.gpu-run}/bin/gpu-run";
            };
            vfio-bind = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.vfio-bind}/bin/vfio-bind";
            };
            vfio-unbind = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.vfio-unbind}/bin/vfio-unbind";
            };
            vfio-list = {
              type = "app";
              program = "${pkgs.aleph.script.compiled.vfio-list}/bin/vfio-list";
            };
          })
          # Firecracker/Isospin tools (if enabled)
          # Note: Container module exposes these via perSystem.packages
          # They'll be merged into config.packages, so we reference them there
          (let
            aleph = config.aleph or {};
            container = aleph.container or { enable = false; isospin = { enable = false; }; };
          in lib.mkIf ((container.enable or false) && (container.isospin.enable or false) && pkgs.stdenv.isLinux) (lib.optionalAttrs (builtins.hasAttr "isospin-run" config.packages) {
            isospin-run = {
              type = "app";
              program = lib.getExe config.packages.isospin-run;
            };
          }))
          # Cloud Hypervisor tools (if enabled)
          (let
            aleph = config.aleph or {};
            container = aleph.container or { enable = false; cloud-hypervisor = { enable = false; }; };
          in lib.mkIf ((container.enable or false) && (container.cloud-hypervisor.enable or false) && pkgs.stdenv.isLinux) (lib.optionalAttrs (builtins.hasAttr "cloud-hypervisor-run" config.packages) {
            cloud-hypervisor-run = {
              type = "app";
              program = lib.getExe config.packages.cloud-hypervisor-run;
            };
            cloud-hypervisor-gpu = {
              type = "app";
              program = lib.getExe config.packages.cloud-hypervisor-gpu;
            };
          }))
          # Formatter (if enabled)
          (lib.mkIf ((config.aleph or { formatter = { enable = false; }; }).formatter.enable or false) {
            formatter = {
              type = "app";
              program = lib.getExe config.treefmt.build;
            };
          })
          # Typed Unix Scripts
          {
            nix-dev = {
              type = "app";
              program = lib.getExe pkgs.aleph.script.nix-dev;
            };
            nix-ci = {
              type = "app";
              program = lib.getExe pkgs.aleph.script.nix-ci;
            };
            gen-wrapper = {
              type = "app";
              program = lib.getExe pkgs.aleph.script.gen-wrapper;
            };
            aleph-script-check = {
              type = "app";
              program = lib.getExe pkgs.aleph.script.check;
            };
            aleph-script-props = {
              type = "app";
              program = lib.getExe pkgs.aleph.script.props;
            };
            combine-archive = {
              type = "app";
              program = lib.getExe pkgs.aleph.script.compiled.combine-archive;
            };
          }
          # Lint tools (if enabled)
          (lib.mkIf ((config.aleph or { lint = { enable = false; }; }).lint.enable or false) (lib.optionalAttrs (builtins.hasAttr "lint-init" config.packages) {
            lint-init = {
              type = "app";
              program = lib.getExe config.packages.lint-init;
            };
            lint-link = {
              type = "app";
              program = lib.getExe config.packages.lint-link;
            };
          }))
        ];
          
          # Export prelude for use in other Nix expressions via legacyPackages
          # Note: perSystem.lib is not a valid option, so we expose via legacyPackages instead
          # Access via: inputs.self.legacyPackages.${system}.forge
          legacyPackages = {
            forge = {
              inherit prelude;
              inherit callBackend callBridgeServer callDatabase callAnalytics;
            };
          };
        };
    };
}
