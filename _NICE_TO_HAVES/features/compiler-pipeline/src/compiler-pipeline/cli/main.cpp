// CLI Tool: Complete Compiler Pipeline
#include <iostream>
#include <string>
#include <vector>
#include <filesystem>
#include <fstream>

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: compiler-pipeline <command> [options]\n";
        std::cerr << "\nCommands:\n";
        std::cerr << "  compile <input> <output-dir> [--lang=purescript|haskell|lean4]\n";
        std::cerr << "  generate-react <cpp-file> <output-dir>\n";
        std::cerr << "  build-wasm <cpp-file> <output-file>\n";
        return 1;
    }

    std::string command = argv[1];

    if (command == "compile") {
        if (argc < 4) {
            std::cerr << "Error: compile requires input file and output directory\n";
            return 1;
        }

        std::string input_file = argv[2];
        std::string output_dir = argv[3];
        std::string lang = "purescript";

        // Parse language option
        for (int i = 4; i < argc; ++i) {
            std::string arg = argv[i];
            if (arg.find("--lang=") == 0) {
                lang = arg.substr(7);
            }
        }

        std::filesystem::create_directories(output_dir);

        if (lang == "purescript") {
            // Call PureScript → C++23 compiler
            std::string cmd = "purescript-to-cpp23 compile \"" + input_file + "\" \"" + output_dir + "\"";
            int result = system(cmd.c_str());
            if (result != 0) {
                std::cerr << "Error: PureScript compilation failed\n";
                return 1;
            }
        } else if (lang == "haskell") {
            // Call Haskell → C++23 compiler
            std::string cmd = "haskell-to-cpp23 compile \"" + input_file + "\" \"" + output_dir + "\"";
            int result = system(cmd.c_str());
            if (result != 0) {
                std::cerr << "Error: Haskell compilation failed\n";
                return 1;
            }
        } else if (lang == "lean4") {
            // Call Lean4 → C++23 compiler
            std::string cmd = "lean4-to-cpp23 compile \"" + input_file + "\" \"" + output_dir + "\"";
            int result = system(cmd.c_str());
            if (result != 0) {
                std::cerr << "Error: Lean4 compilation failed\n";
                return 1;
            }
        } else {
            std::cerr << "Error: Unknown language: " << lang << "\n";
            return 1;
        }

        // Then generate React code
        std::string cpp_file = output_dir + "/generated.cpp";
        std::string cmd = "cpp23-to-react \"" + cpp_file + "\" \"" + output_dir + "/react\"";
        int result = system(cmd.c_str());
        if (result != 0) {
            std::cerr << "Error: React generation failed\n";
            return 1;
        }

        std::cout << "Compilation complete!\n";
        std::cout << "  C++23: " << cpp_file << "\n";
        std::cout << "  React: " << output_dir << "/react/\n";

    } else if (command == "generate-react") {
        if (argc < 4) {
            std::cerr << "Error: generate-react requires C++ file and output directory\n";
            return 1;
        }

        std::string cpp_file = argv[2];
        std::string output_dir = argv[3];

        std::filesystem::create_directories(output_dir);

        std::string cmd = "cpp23-to-react \"" + cpp_file + "\" \"" + output_dir + "\"";
        int result = system(cmd.c_str());
        if (result != 0) {
            std::cerr << "Error: React generation failed\n";
            return 1;
        }

        std::cout << "React code generated in: " << output_dir << "\n";

    } else if (command == "build-wasm") {
        if (argc < 4) {
            std::cerr << "Error: build-wasm requires C++ file and output file\n";
            return 1;
        }

        std::string cpp_file = argv[2];
        std::string output_file = argv[3];

        std::string cmd = "emcc -std=c++23 -O2 -s WASM=1 "
                         "-s EXPORTED_FUNCTIONS='[\"_registerCppComponent\",\"_createCppComponent\"]' "
                         "-s EXPORTED_RUNTIME_METHODS='[\"ccall\",\"cwrap\"]' "
                         "-o \"" + output_file + ".js\" \"" + cpp_file + "\"";

        int result = system(cmd.c_str());
        if (result != 0) {
            std::cerr << "Error: WASM compilation failed\n";
            return 1;
        }

        std::cout << "WASM module built: " << output_file << ".js\n";

    } else {
        std::cerr << "Error: Unknown command: " << command << "\n";
        return 1;
    }

    return 0;
}
