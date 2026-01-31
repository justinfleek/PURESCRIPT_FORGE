# Root BUCK file for CODER workspace
#
# This file defines the top-level Buck2 targets for the CODER project.
# Individual projects have their own BUCK files in subdirectories.

# Load toolchains
load("@toolchains//:haskell.bzl", "haskell_binary", "haskell_library")
load("@toolchains//:lean.bzl", "lean_library")
load("@toolchains//:cxx.bzl", "cxx_binary", "cxx_library")

# Example: Build rules-hs with Buck2
# haskell_library(
#     name = "rules-hs",
#     srcs = glob(["src/rules-hs/**/*.hs"]),
#     packages = [
#         "base",
#         "containers",
#         "text",
#     ],
#     visibility = ["PUBLIC"],
# )

# Example: Build rules-lean with Buck2
# lean_library(
#     name = "rules-lean",
#     srcs = glob(["src/rules-lean/**/*.lean"]),
#     visibility = ["PUBLIC"],
# )

# Note: PureScript projects currently use Spago/Nix builds.
# Buck2 support for PureScript can be added later if needed.
