// Main entry point for C++23 → React generator
#include "ReactGenerator.h"
#include "Cpp23Parser.h"
#include <iostream>
#include <string>
#include <filesystem>

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: cpp23-to-react <input.cpp> <output-dir>\n";
        return 1;
    }

    std::string input_file = argv[1];
    std::string output_dir = argv[2];

    try {
        // Parse C++23 file
        std::vector<CppStruct> components = parseCpp23File(input_file);
        
        if (components.empty()) {
            std::cerr << "Warning: No components found in " << input_file << "\n";
            return 0;
        }

        // Generate React code
        react_generator::generate_react_code(components, output_dir);

        std::cout << "Generated " << components.size() << " React components in " 
                  << output_dir << "\n";
        
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}
