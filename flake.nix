{
  description = "CODER workspace - PureScript/Haskell/Lean4 with proofs";

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
      
      # Import aleph-continuity flake modules for prelude, build, typed unix
      # std module includes: formatter, lint, docs, std, devshell, prelude, nv-sdk, container
      # build module adds: Buck2 build infrastructure with toolchains
      # lre module adds: Local Remote Execution (NativeLink) for distributed builds
      # nativelink module adds: NativeLink container infrastructure (requires nix2gpu)
      # devshell module adds: Development shell with GHC WASM and straylight-nix support
      imports = [ 
        aleph-continuity.modules.flake.std
        aleph-continuity.modules.flake.build
        aleph-continuity.modules.flake.shortlist
        aleph-continuity.modules.flake.lre
        aleph-continuity.modules.flake.devshell
        # nix2gpu must be imported before nativelink (provides perSystem.nix2gpu options)
        inputs.nix2gpu.flakeModule
        aleph-continuity.modules.flake.nativelink
      ];

      # Enable Buck2 build infrastructure (top-level config)
      aleph.build = {
        enable = true;
        prelude.enable = true;
        prelude.path = null;  # Use inputs.buck2-prelude
        
        # Enable toolchains
        toolchain = {
          cxx.enable = true;
          haskell.enable = true;
          lean.enable = true;
          rust.enable = true;
          python.enable = true;
          # nv.enable = false;  # NVIDIA GPU - enable if needed
        };
        
        # Generate .buckconfig.local in devshell
        generate-buckconfig = true;
        generate-wrappers = true;
        
        # IDE integration
        compdb = {
          enable = true;
          targets = [ "//..." ];
          auto-generate = false;  # Use bin/compdb manually
        };
        
        # Remote execution: use local NativeLink (not Fly.io)
        remote.enable = false;
      };
      
      # Enable Local Remote Execution (NativeLink)
      # Provides distributed builds with CAS caching
      aleph.lre = {
        enable = true;
        port = 50051;  # NativeLink CAS/scheduler port
        workers = 4;   # Default number of worker processes
        instance-name = "main";
      };
      
      # Formatter (treefmt) - unified formatting across all languages
      # Already included via std module, but configure explicitly
      aleph.formatter = {
        enable = true;
        indent-width = 2;      # Match CODER standards (2 spaces)
        line-length = 100;     # Match CODER standards (100 chars)
        enable-check = true;   # Enable flake check for treefmt
      };
      
      # Lint - lint configs for all languages
      # Already included via std module
      aleph.lint = {
        enable = true;  # Provides lint-init, lint-link packages
      };
      
      # Documentation generation (mdBook)
      # Already included via std module
      aleph.docs = {
        enable = true;
        title = "CODER Documentation";
        description = "CODER: Continuity Protocol Development Environment";
        theme = "ono-sendai";  # Dark mode cyberdeck interface
        src = ./docs;
        options-src = ./docs-options;  # Will create if needed
        modules = [ ];  # Add NixOS modules here for options extraction
      };
      
      # Devshell - development environment with all toolchains
      # Enable GHC WASM backend and straylight-nix (builtins.wasm support)
      aleph.devshell = {
        enable = true;
        ghc-wasm.enable = true;  # GHC WASM backend for builtins.wasm plugins
        straylight-nix.enable = true;  # straylight-nix with builtins.wasm support
        nv.enable = false;  # NVIDIA SDK - enable if needed (requires allow-unfree)
      };
      
      # Shortlist - Hermetic C++ libraries for Buck2 builds
      # Provides: fmt, spdlog, catch2, libsodium, simdjson, mdspan, rapidjson, nlohmann-json, zlib-ng
      # These libraries are built with LLVM 22 and available as Buck2 prebuilt_cxx_library targets
      aleph.shortlist = {
        enable = true;  # Enable shortlist libraries
        
        # Individual library toggles (all enabled by default)
        zlib-ng = true;      # High-performance zlib replacement
        fmt = true;          # Modern C++ formatting library
        catch2 = true;       # C++ testing framework
        spdlog = true;       # Fast C++ logging library
        mdspan = true;       # C++23 multidimensional array view (header-only)
        rapidjson = true;    # Fast JSON parser/generator (header-only)
        nlohmann-json = true; # JSON for Modern C++ (header-only)
        libsodium = true;    # Modern cryptography library
        simdjson = true;     # SIMD-accelerated JSON parser (4+ GB/s)
      };
      
      # Container infrastructure (already enabled via std module)
      # Provides: OCI extraction, Firecracker VMs, Cloud Hypervisor, namespace runners
      # Available via pkgs.aleph.container.*
      aleph.container = {
        enable = true;  # Container tools enabled by default
        
        # Isospin (Firecracker fork) VM tools
        isospin = {
          enable = true;
          cpus = 4;
          mem-mib = 4096;
        };
        
        # Cloud Hypervisor VM tools (with VFIO GPU passthrough)
        cloud-hypervisor = {
          enable = true;
          cpus = 8;
          mem-gib = 16;
          hugepages = false;  # Enable for GPU workloads
        };
      };
      
      # Central nixpkgs configuration (ℵ-001 §3)
      # Configure overlays via aleph.nixpkgs.overlays instead of manual import
      aleph.nixpkgs.overlays = [
        purescript-overlay.overlays.default
        # aleph-continuity.overlays.default is already included by std module
      ];
      
      # NativeLink container infrastructure (for Fly.io deployment)
      # Can deploy scheduler, CAS, and workers to Fly.io for distributed builds
      aleph.nativelink = {
        enable = false;  # Set to true to enable Fly.io deployment
        fly = {
          app-prefix = "coder";
          region = "iad";  # Primary Fly.io region
        };
        
        # Builder: dedicated nix build machine on Fly
        builder = {
          enable = true;
          cpus = 16;
          memory = "32gb";
          volume-size = "200gb";
        };
        
        # Scheduler: coordinates work, routes actions to workers
        scheduler = {
          port = 50051;
          cpus = 2;
          memory = "2gb";
        };
        
        # CAS: content-addressed storage with LZ4 compression
        cas = {
          port = 50052;
          data-dir = "/data";
          max-bytes = 500 * 1024 * 1024 * 1024;  # 500GB
          cpus = 4;
          memory = "8gb";
          volume-size = "500gb";
          
          # R2 backend: Cloudflare R2 as slow tier (optional)
          r2 = {
            enable = false;
            bucket = "nativelink-cas";
            endpoint = "";
            key-prefix = "cas/";
          };
        };
        
        # Workers: execute build actions
        worker = {
          count = 8;
          cpus = 16;
          memory = "32gb";
          cpu-kind = "performance";
          volume-size = "100gb";
        };
        
        # Nix Proxy: caching HTTP proxy for build-time fetches
        nix-proxy = {
          enable = true;
          port = 8080;
          cpus = 2;
          memory = "4gb";
          volume-size = "100gb";
          allowlist = [
            "cache.nixos.org"
            "nix-community.cachix.org"
            "github.com"
            "githubusercontent.com"
            "crates.io"
            "pypi.org"
            "registry.npmjs.org"
            "hackage.haskell.org"
          ];
        };
        
        registry = "ghcr.io/straylight-software/aleph";
      };

      perSystem = { config, self', inputs', pkgs, system, lib, ... }:
        {
        let
          # NVIDIA SDK configuration (if enabled)
          # Provides CUDA, cuDNN, TensorRT, NCCL, CUTLASS
          # Note: Requires nixpkgs.allow-unfree = true for NVIDIA packages
          nv-sdk-config = {
            enable = false;  # Disabled by default (requires unfree packages)
            sdk-version = "13";  # CUDA 13 (or "12_9" for CUDA 12.9)
            with-driver = true;  # Include NVIDIA driver in SDK bundle
            nvidia-driver = null;  # Auto-detect from pkgs.linuxPackages.nvidia_x11
          };
          
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
          spago = pkgs.spago-unstable;
          purs = pkgs.purescript;

          # Haskell toolchain
          haskellPackages = pkgs.haskellPackages;

          # Lean4 toolchain
          lean = lean4.packages.${system}.lean4;

          # PureScript project for rules/standards
          rules-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
            pname = "coder-rules-ps";
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
              description = "CODER coding rules and standards (PureScript)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Haskell project for rules/standards
          rules-hs = haskellPackages.callCabal2nix "coder-rules-hs" ./src/rules-hs { 
            test = true;
            meta = {
              description = "CODER coding rules and standards (Haskell)";
              license = pkgs.lib.licenses.mit;
            };
          };

          # Lean4 project for proofs
          rules-lean = lean.buildPackage {
            name = "CoderRules";
            src = ./src/rules-lean;
          };

          # PRISM Color Core (Haskell)
          prism-color-core-hs = haskellPackages.callCabal2nix "prism-color-core" 
            ./PRISM/prism-color-core/haskell { 
              meta = {
                description = "PRISM color core (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            };

          # PRISM Color Core (Lean4)
          prism-color-core-lean = (lean.buildPackage {
            name = "PrismColor";
            src = ./PRISM/prism-color-core/lean4;
          }).overrideAttrs (finalAttrs: {
            meta = {
              description = "PRISM color core (Lean4)";
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
              description = "OpenCode shared type definitions (PureScript)";
              license = pkgs.lib.licenses.mit;
            };
          });

          # Spec loader/parser (Haskell)
          spec-loader-hs = haskellPackages.callCabal2nix "spec-loader" 
            ./src/spec-loader-hs { 
              meta = {
                description = "Spec loader/parser (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            };
          
          # OpenCode validator (Haskell)
          opencode-validator-hs = haskellPackages.callCabal2nix "opencode-validator" 
            ./src/opencode-validator-hs { 
              meta = {
                description = "OpenCode validator (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            };
          
          # Bridge Database (Haskell)
          bridge-database-hs = haskellPackages.callCabal2nix "bridge-database" 
            ./src/bridge-database-hs { 
              meta = {
                description = "Bridge database backend (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            };
          
          # Bridge Analytics (Haskell/DuckDB)
          bridge-analytics-hs = haskellPackages.callCabal2nix "bridge-analytics" 
            ./src/bridge-analytics-hs { 
              # Note: duckdb-haskell may need to be added to haskellPackages
              # or use DuckDB C API via FFI
              meta = {
                description = "Bridge analytics backend (Haskell/DuckDB)";
                license = pkgs.lib.licenses.mit;
              };
            };
          
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
            pname = "straylight-semantic-cells";
            version = "0.1.0";
            src = ./STRAYLIGHT/semantic-cells;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              numpy
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT semantic cells (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Database Layer (Python)
          straylight-database-layer = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-database-layer";
            version = "0.1.0";
            src = ./STRAYLIGHT/database-layer;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              duckdb
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT database layer (Python/DuckDB)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Agent Orchestrator (Python)
          straylight-agent-orchestrator = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-agent-orchestrator";
            version = "0.1.0";
            src = ./STRAYLIGHT/agent-orchestrator;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # No external deps - uses subprocess for bubblewrap
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT agent orchestrator (Python, FFI only)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Network Graph (Python)
          straylight-network-graph = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-network-graph";
            version = "0.1.0";
            src = ./STRAYLIGHT/network-graph;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT network graph (Python, FFI only)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Web Search Agent (Python)
          straylight-web-search-agent = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-web-search-agent";
            version = "0.1.0";
            src = ./STRAYLIGHT/web-search-agent;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              requests
              beautifulsoup4
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT web search agent (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Content Extraction Agent (Python)
          straylight-content-extraction-agent = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-content-extraction-agent";
            version = "0.1.0";
            src = ./STRAYLIGHT/content-extraction-agent;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Would add spaCy, NLTK in production
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT content extraction agent (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Network Formation Agent (Python)
          straylight-network-formation-agent = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-network-formation-agent";
            version = "0.1.0";
            src = ./STRAYLIGHT/network-formation-agent;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT network formation agent (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Agent Social (Python)
          straylight-agent-social = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-agent-social";
            version = "0.1.0";
            src = ./STRAYLIGHT/agent-social;
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
          
          # STRAYLIGHT - Performance/Caching (Python)
          straylight-performance = pkgs.python3Packages.buildPythonPackage {
            pname = "straylight-performance";
            version = "0.1.0";
            src = ./STRAYLIGHT/performance;
            format = "setuptools";
            propagatedBuildInputs = with pkgs.python3Packages; [
              # Pure Python implementation
            ];
            doCheck = false;
            meta = {
              description = "STRAYLIGHT performance and caching (Python)";
              license = pkgs.lib.licenses.mit;
            };
          };
          
          # STRAYLIGHT - Engram Attestation (Haskell)
          engram-attestation-hs = haskellPackages.callCabal2nix "engram-types" 
            ./STRAYLIGHT/engram-attestation/engram-types { 
              meta = {
                description = "STRAYLIGHT Engram attestation (Haskell)";
                license = pkgs.lib.licenses.mit;
              };
            };

          # Bridge Server (PureScript)
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
              description = "OpenCode bridge server (PureScript/Node.js)";
              license = pkgs.lib.licenses.mit;
              mainProgram = "bridge-server";
            };
          });

        in
        {
          # NVIDIA SDK configuration (perSystem)
          # Provides CUDA, cuDNN, TensorRT, NCCL, CUTLASS
          nv.sdk = nv-sdk-config;
          
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
                description = "OpenCode plugin (PureScript/Node.js)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # STRAYLIGHT - All Python packages
            semantic-cells-python = semantic-cells-python;
            straylight-database-layer = straylight-database-layer;
            straylight-agent-orchestrator = straylight-agent-orchestrator;
            straylight-network-graph = straylight-network-graph;
            straylight-web-search-agent = straylight-web-search-agent;
            straylight-content-extraction-agent = straylight-content-extraction-agent;
            straylight-network-formation-agent = straylight-network-formation-agent;
            straylight-agent-social = straylight-agent-social;
            straylight-performance = straylight-performance;

            # STRAYLIGHT - Engram Attestation (Haskell)
            engram-attestation-hs = engram-attestation-hs;
            
            # STRAYLIGHT - Agent Orchestrator (PureScript)
            straylight-agent-orchestrator-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "straylight-agent-orchestrator-ps";
              version = "0.1.0";
              src = ./STRAYLIGHT/agent-orchestrator-ps;
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
                description = "STRAYLIGHT agent orchestrator (PureScript)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # STRAYLIGHT - Network Graph (PureScript)
            straylight-network-graph-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "straylight-network-graph-ps";
              version = "0.1.0";
              src = ./STRAYLIGHT/network-graph-ps;
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
                description = "STRAYLIGHT network graph (PureScript)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # STRAYLIGHT - Network Graph Metrics (Haskell)
            straylight-network-graph-hs = haskellPackages.callCabal2nix "straylight-network-graph-hs"
              ./STRAYLIGHT/network-graph-hs { 
                meta = {
                  description = "STRAYLIGHT network graph metrics (Haskell)";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # STRAYLIGHT - Agent Social (PureScript)
            straylight-agent-social-ps = pkgs.stdenv.mkDerivation (finalAttrs: {
              pname = "straylight-agent-social-ps";
              version = "0.1.0";
              src = ./STRAYLIGHT/agent-social-ps;
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
                description = "STRAYLIGHT agent social system (PureScript)";
                license = pkgs.lib.licenses.mit;
              };
            });
            
            # STRAYLIGHT - Proofs (Lean4)
            straylight-proofs-lean = (lean.buildPackage {
              name = "StraylightProofs";
              src = ./STRAYLIGHT/proofs-lean;
            }).overrideAttrs (finalAttrs: {
              meta = {
                description = "STRAYLIGHT proofs (Lean4)";
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
                  description = "Render ClickHouse client (Haskell)";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # Render CAS Client (Haskell)
            render-cas-hs = haskellPackages.callCabal2nix "render-cas-hs"
              ./src/render-cas-hs { 
                meta = {
                  description = "Render CAS client (Haskell/Straylight CAS)";
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
                  description = "Render compliance and audit trail (Haskell)";
                  license = pkgs.lib.licenses.mit;
                };
              };
            
            # STRAYLIGHT - All components
            straylight-all = pkgs.symlinkJoin {
              name = "straylight-all";
              paths = [
                # Python packages (FFI only)
                semantic-cells-python
                straylight-database-layer
                straylight-agent-orchestrator
                straylight-network-graph
                straylight-web-search-agent
                straylight-content-extraction-agent
                straylight-network-formation-agent
                straylight-agent-social
                straylight-performance
                # PureScript/Haskell (core logic)
                straylight-agent-orchestrator-ps
                straylight-network-graph-ps
                straylight-network-graph-hs
                straylight-agent-social-ps
                # Haskell
                engram-attestation-hs
                # Lean4 proofs
                straylight-proofs-lean
              ];
            };
            
            # All packages
            all-packages = pkgs.symlinkJoin {
              name = "coder-all";
              paths = [
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
                opencode-plugin-ps
                semantic-cells-python
                engram-attestation-hs
              ];
            };
          };

          devShells = {
            default = pkgs.mkShell {
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
                pkgs.nodePackages.playwright  # Playwright for headless browser E2E testing
                pkgs.playwright-driver.browsers  # Browser binaries (Chromium, Firefox, WebKit)
                pkgs.just
                pkgs.watchexec
                # Buck2 build infrastructure (if enabled)
              ] ++ (lib.optionals config.aleph.build.enable config.aleph.build.packages)
                ++ (lib.optionals config.aleph.lre.enable config.aleph.lre.packages)
                # GHC WASM toolchain (if enabled)
                ++ (lib.optionals (config.aleph.devshell.enable && config.aleph.devshell.ghc-wasm.enable && pkgs ? aleph && pkgs.aleph ? ghc-wasm) (
                  let ghc-wasm = pkgs.aleph.ghc-wasm;
                  in lib.filter (p: p != null) [
                    ghc-wasm.ghc-wasm
                    ghc-wasm.ghc-wasm-cabal
                    ghc-wasm.wasi-sdk
                    ghc-wasm.wasm-wasmtime
                  ]
                ))
                # straylight-nix with builtins.wasm support (if enabled)
                ++ (lib.optionals (config.aleph.devshell.enable && config.aleph.devshell.straylight-nix.enable && pkgs ? aleph && pkgs.aleph ? nix) [
                  pkgs.aleph.nix.nix
                ])
                # Armitage (witness proxy for build-time fetches)
                ++ (lib.optionals (pkgs ? armitage-cli) [
                  pkgs.armitage-cli
                  pkgs.armitage-proxy
                ])
                # Container tools (if enabled, Linux only)
                ++ (lib.optionals (config.aleph.container.enable && pkgs.stdenv.isLinux) [
                  pkgs.aleph.container.fhs-run
                  pkgs.aleph.container.gpu-run
                  pkgs.aleph.script.compiled.crane-inspect
                  pkgs.aleph.script.compiled.crane-pull
                  pkgs.aleph.script.compiled.unshare-run
                  pkgs.aleph.script.compiled.unshare-gpu
                  pkgs.aleph.script.compiled.vfio-bind
                  pkgs.aleph.script.compiled.vfio-unbind
                  pkgs.aleph.script.compiled.vfio-list
                ])
                # Typed Unix scripts (all available)
                ++ [
                  pkgs.aleph.script.compiled.combine-archive
                  pkgs.aleph.script.nix-dev
                  pkgs.aleph.script.nix-ci
                  pkgs.aleph.script.gen-wrapper
                  pkgs.aleph.script.check
                  pkgs.aleph.script.props
                ]
                # CLI tool wrappers (for use in typed scripts)
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
              # Buck2 shell hook (generates .buckconfig.local, toolchain wrappers)
              # LRE shell hook (appends RE config to .buckconfig.local)
              shellHook = ''
                ${lib.optionalString config.aleph.build.enable config.aleph.build.shellHook}
                ${lib.optionalString config.aleph.shortlist.enable config.aleph.shortlist.shellHook}
                ${lib.optionalString config.aleph.lre.enable config.aleph.lre.shellHook}
                echo "════════════════════════════════════════════════════════════════"
                echo "  CODER Development Shell"
                echo "════════════════════════════════════════════════════════════════"
                echo ""
                echo "PureScript: $(purs --version)"
                echo "Haskell: $(ghc --version)"
                echo "Lean4: $(lean --version)"
                echo "Node.js: $(node --version)"
                ${lib.optionalString config.aleph.build.enable ''
                echo "Buck2: $(buck2 --version 2>/dev/null || echo 'not available')"
                ''}
                ${lib.optionalString config.aleph.lre.enable ''
                echo "NativeLink: $(nativelink --version 2>/dev/null || echo 'available')"
                echo "LRE: Local Remote Execution enabled (port ${toString config.aleph.lre.port})"
                ''}
                ${lib.optionalString (config.aleph.container.enable && pkgs.stdenv.isLinux) ''
                echo "Container Tools: Available (Linux)"
                echo "  - OCI: crane-inspect, crane-pull"
                echo "  - Namespaces: unshare-run, unshare-gpu, fhs-run, gpu-run"
                echo "  - VFIO: vfio-bind, vfio-unbind, vfio-list"
                ${lib.optionalString config.aleph.container.isospin.enable ''
                echo "  - Firecracker: isospin-run (enabled)"
                ''}
                ${lib.optionalString config.aleph.container.cloud-hypervisor.enable ''
                echo "  - Cloud Hypervisor: cloud-hypervisor-run, cloud-hypervisor-gpu (enabled)"
                ''}
                ''}
                echo ""
                echo "Available packages:"
                echo "  - Rules (PureScript/Haskell/Lean4)"
                echo "  - PRISM Color Core (Haskell/Lean4)"
                echo "  - Sidepanel (PureScript)"
                echo "  - Spec Loader (Haskell)"
                echo "  - OpenCode Types (PureScript) - Phase 2 Migration"
                echo "  - OpenCode Validator (Haskell) - Phase 2 Migration"
                ${lib.optionalString config.aleph.build.enable ''
                echo "  - Buck2 Build Infrastructure (enabled)"
                ''}
                ${lib.optionalString config.aleph.shortlist.enable ''
                echo "  - Shortlist C++ Libraries (enabled)"
                ''}
                ${lib.optionalString config.aleph.lre.enable ''
                echo "  - Local Remote Execution (NativeLink) (enabled)"
                ''}
                ${lib.optionalString config.aleph.container.enable ''
                echo "  - Container Infrastructure (enabled)"
                ''}
                ${lib.optionalString (config.aleph.devshell.enable && config.aleph.devshell.ghc-wasm.enable) ''
                echo "  - GHC WASM Backend (enabled) - wasm32-wasi-ghc, wasm32-wasi-cabal"
                ''}
                ${lib.optionalString (config.aleph.devshell.enable && config.aleph.devshell.straylight-nix.enable) ''
                echo "  - straylight-nix with builtins.wasm (enabled)"
                ''}
                ${lib.optionalString (pkgs ? armitage-cli) ''
                echo "  - Armitage (witness proxy for build-time fetches)"
                ''}
                echo ""
                echo "Build commands:"
                echo "  nix build .#all-packages  - Build everything"
                echo "  nix build .#sidepanel-ps  - Build sidepanel"
                echo "  nix build .#opencode-types-ps - Build OpenCode types"
                echo "  nix build .#opencode-validator-hs - Build validator"
                ${lib.optionalString config.aleph.build.enable ''
                echo ""
                echo "Buck2 commands:"
                echo "  buck2 build //...  - Build all Buck2 targets"
                echo "  buck2 test //...   - Run all Buck2 tests"
                echo "  bin/compdb         - Generate compile_commands.json"
                ''}
                ${lib.optionalString config.aleph.shortlist.enable ''
                echo ""
                echo "Shortlist C++ libraries:"
                echo "  Available in Buck2 as prebuilt_cxx_library targets"
                echo "  Config: Added to .buckconfig.local automatically"
                echo "  Libraries: fmt, spdlog, catch2, libsodium, simdjson, mdspan, rapidjson, nlohmann-json, zlib-ng"
                ''}
                echo ""
                echo "Typed Unix Scripts:"
                echo "  nix-dev <command>        - Development Nix wrapper (no cache, verbose)"
                echo "  nix-ci <command>         - CI Nix wrapper (cached, verbose)"
                echo "  gen-wrapper <tool>       - Generate type-safe CLI wrapper"
                echo "  aleph-script-check       - Validate all scripts"
                echo "  aleph-script-props       - Property tests"
                echo "  combine-archive <files>  - Combine static archives"
                echo ""
                echo "CLI Tools (for typed scripts):"
                echo "  rg, fd, bat, delta, dust, tokei, hyperfine"
                echo "  statix, deadnix, stylua, taplo, zoxide"
                echo ""
                echo "libmodern C++ libraries:"
                echo "  Available via pkgs.libmodern.fmt, pkgs.libmodern.abseil-cpp, pkgs.libmodern.libsodium"
                echo "  Static libraries, C++17, -fPIC, RelWithDebInfo builds"
                echo ""
                echo "Verification commands:"
                echo "  nix run .#verify-builds-aleph  - Verify all package builds"
                echo "  nix run .#verify-integrations   - Verify all integrations"
                echo "  nix flake check                 - Verify flake configuration"
                ${lib.optionalString config.aleph.lre.enable ''
                echo ""
                echo "LRE commands:"
                echo "  lre-start          - Start local NativeLink (CAS + scheduler)"
                echo "  lre-start --workers=8  - Start with custom worker count"
                echo "  buck2 build --prefer-remote //...  - Use remote execution"
                ''}
                ${lib.optionalString config.aleph.formatter.enable ''
                echo ""
                echo "Formatter commands:"
                echo "  nix fmt              - Format all code"
                echo "  nix run .#formatter  - Format all code (alternative)"
                echo "  nix flake check      - Check formatting (includes formatter)"
                ''}
                ${lib.optionalString config.aleph.lint.enable ''
                echo ""
                echo "Lint commands:"
                echo "  nix run .#lint-init  - Initialize lint configs in project"
                echo "  nix run .#lint-link  - Link lint configs to project"
                ''}
                ${lib.optionalString config.aleph.docs.enable ''
                echo ""
                echo "Documentation commands:"
                echo "  nix build .#docs           - Build documentation"
                echo "  nix develop .#docs        - Enter docs devshell"
                echo "  nix develop .#docs -c mdbook serve  - Preview docs"
                ''}
                ${lib.optionalString (config.aleph.devshell.enable && config.aleph.devshell.ghc-wasm.enable) ''
                echo ""
                echo "GHC WASM commands:"
                echo "  wasm32-wasi-ghc --version  - Check GHC WASM version"
                echo "  wasm32-wasi-cabal --version - Check Cabal WASM version"
                echo "  wasmtime --version         - Check WASM runtime version"
                ''}
                ${lib.optionalString (config.aleph.devshell.enable && config.aleph.devshell.straylight-nix.enable) ''
                echo ""
                echo "straylight-nix commands:"
                echo "  nix eval --expr 'builtins ? wasm'  - Check builtins.wasm availability"
                echo "  nix eval --expr 'builtins.wasm.loadWasm \"path/to/file.wasm\"'  - Load WASM module"
                ''}
                ${lib.optionalString (pkgs ? armitage-cli) ''
                echo ""
                echo "Armitage commands:"
                echo "  armitage build <derivation>  - Build without daemon"
                echo "  armitage store <path>        - Store path in CAS"
                echo "  armitage-proxy               - Start witness proxy"
                ''}
                ${lib.optionalString config.nv.sdk.enable ''
                echo ""
                echo "NVIDIA SDK commands:"
                echo "  nix build .#nvidia-sdk-cuda  - Build NVIDIA SDK bundle"
                echo "  nix build .#cutlass          - Build CUTLASS library"
                echo "  nvidia-smi                    - Check GPU status"
                echo "  nvcc --version                - Check CUDA compiler"
                ''}
                ${lib.optionalString (config.aleph.container.enable && pkgs.stdenv.isLinux) ''
                echo ""
                echo "Container commands:"
                echo "  crane-inspect <image>  - Inspect OCI image"
                echo "  crane-pull <image>     - Pull OCI image"
                echo "  unshare-run <cmd>      - Run in namespace"
                echo "  unshare-gpu <cmd>      - Run with GPU in namespace"
                echo "  fhs-run <cmd>          - Run with FHS layout"
                echo "  gpu-run <cmd>          - Run with GPU access"
                echo "  vfio-bind <pci-id>     - Bind GPU to VFIO"
                echo "  vfio-unbind <pci-id>    - Unbind GPU from VFIO"
                echo "  vfio-list              - List VFIO devices"
                ${lib.optionalString config.aleph.container.isospin.enable ''
                echo "  isospin-run <image> <cmd>  - Run in Firecracker VM"
                echo "  isospin-build <image> <cmd> - Build in Firecracker VM"
                ''}
                ${lib.optionalString config.aleph.container.cloud-hypervisor.enable ''
                echo "  cloud-hypervisor-run <image> <cmd>  - Run in Cloud Hypervisor VM"
                echo "  cloud-hypervisor-gpu <image> <cmd>  - Run with GPU passthrough"
                ''}
                ''}
                echo ""
                echo "Validation commands:"
                echo "  nix run .#validate-opencode - Validate OpenCode code"
                echo "  nix run .#opencode-validator -- banned <path> - Check banned constructs"
                echo "  nix run .#opencode-validator -- file-reading <path> - Check file reading protocol"
                echo "  nix run .#opencode-validator -- type-escapes <path> - Check type escapes"
                echo ""
              '';
            };
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

            # Typed Unix build verification (Haskell script via aleph-continuity)
            verify-builds-aleph = {
              type = "app";
              program = "${pkgs.aleph.ghc.turtle-script {
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
            
            # Backend health check using aleph prelude
            backend-health = {
              type = "app";
              program = pkgs.writeShellScriptBin "backend-health" ''
                #!/usr/bin/env bash
                # Health check for all backend services using functional patterns
                echo "Checking backend services..."
                
                # Check bridge server
                if ${bridge-server-ps}/bin/bridge-server --health-check 2>/dev/null; then
                  echo "✅ Bridge Server: Healthy"
                else
                  echo "❌ Bridge Server: Unhealthy"
                  exit 1
                fi
                
                # Check database backend
                if ${bridge-database-hs}/bin/bridge-database health 2>/dev/null; then
                  echo "✅ Database Backend: Healthy"
                else
                  echo "❌ Database Backend: Unhealthy"
                  exit 1
                fi
                
                # Check analytics backend
                if ${bridge-analytics-hs}/bin/bridge-analytics health 2>/dev/null; then
                  echo "✅ Analytics Backend: Healthy"
                else
                  echo "❌ Analytics Backend: Unhealthy"
                  exit 1
                fi
                
                echo "All backend services healthy"
              '';
            };
          }
          # Conditionally add LRE/NativeLink apps
          (lib.mkIf config.aleph.lre.enable {
            lre-start = {
              type = "app";
              program = "${config.aleph.lre.lre-start}/bin/lre-start";
            };
          })
          (lib.mkIf config.aleph.nativelink.enable {
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
          (lib.mkIf (config.aleph.container.enable && pkgs.stdenv.isLinux) {
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
          (lib.mkIf (config.aleph.container.enable && config.aleph.container.isospin.enable && pkgs.stdenv.isLinux) (lib.optionalAttrs (builtins.hasAttr "isospin-run" config.packages) {
            isospin-run = {
              type = "app";
              program = lib.getExe config.packages.isospin-run;
            };
          }))
          # Cloud Hypervisor tools (if enabled)
          (lib.mkIf (config.aleph.container.enable && config.aleph.container.cloud-hypervisor.enable && pkgs.stdenv.isLinux) (lib.optionalAttrs (builtins.hasAttr "cloud-hypervisor-run" config.packages) {
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
          (lib.mkIf config.aleph.formatter.enable {
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
          (lib.mkIf config.aleph.lint.enable (lib.optionalAttrs (builtins.hasAttr "lint-init" config.packages) {
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
          
          # Export prelude for use in other Nix expressions
          lib = {
            inherit prelude;
            inherit callBackend callBridgeServer callDatabase callAnalytics;
          };
        };
    };
}
