"use strict";

/**
 * Archive FFI
 * Provides archive utilities (zip creation/extraction)
 */

const fs = require("fs").promises;
const path = require("path");
const { createWriteStream } = require("fs");
const { pipeline } = require("stream/promises");
const archiver = require("archiver");
const extract = require("extract-zip");

// | Create a zip archive
exports.createZipArchive = function (outputPath) {
  return function (files) {
    return function () {
      return new Promise(function (resolve) {
        const output = createWriteStream(outputPath);
        const archive = archiver("zip", { zlib: { level: 9 } });
        
        output.on("close", function () {
          resolve({
            tag: "Right",
            value: outputPath
          });
        });
        
        archive.on("error", function (error) {
          resolve({
            tag: "Left",
            value: error.message || "Failed to create zip archive"
          });
        });
        
        archive.pipe(output);
        
        files.forEach(function (file) {
          archive.file(file, { name: path.basename(file) });
        });
        
        archive.finalize();
      });
    };
  };
};

// | Extract a zip archive
exports.extractZipArchive = function (archivePath) {
  return function (outputDir) {
    return function () {
      return extract(archivePath, { dir: outputDir })
        .then(function () {
          return {
            tag: "Right",
            value: null
          };
        })
        .catch(function (error) {
          return {
            tag: "Left",
            value: error.message || "Failed to extract zip archive"
          };
        });
    };
  };
};
