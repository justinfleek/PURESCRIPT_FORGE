{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Main
-- Description : CLI for prism-theme-generator
-- 
-- Usage:
--   prism-theme-generator generate < config.json > variants.json
--   prism-theme-generator convert --from srgb --to oklch "#ff5733"

module Main where

import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Data.Aeson (encode, object, (.=))
import qualified Data.Text as T

import PrismColor

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["generate"] -> generateMode
    ["convert", "--from", from, "--to", to, color] -> convertMode from to color
    ["--help"] -> printHelp
    ["-h"] -> printHelp
    [] -> printHelp
    _ -> do
      hPutStrLn stderr "Unknown command. Use --help for usage."
      exitFailure

generateMode :: IO ()
generateMode = do
  input <- BL.getContents
  let output = generateThemesFromJSON input
  BL.putStr output
  BL8.putStrLn ""  -- Trailing newline

convertMode :: String -> String -> String -> IO ()
convertMode from to colorStr = do
  case (from, to) of
    ("srgb", "oklch") -> case hexToSrgb colorStr of
      Nothing -> do
        hPutStrLn stderr "Invalid hex color"
        exitFailure
      Just srgb -> do
        let oklch = srgbToOklch srgb
        BL.putStr $ encode $ object
          [ "l" .= unUnit (oklchL oklch)
          , "c" .= oklchC oklch
          , "h" .= unHue (oklchH oklch)
          ]
        BL8.putStrLn ""
    
    ("oklch", "srgb") -> do
      hPutStrLn stderr "OKLCH to sRGB conversion not yet implemented in CLI"
      exitFailure
    
    _ -> do
      hPutStrLn stderr $ "Unsupported conversion: " ++ from ++ " -> " ++ to
      exitFailure

printHelp :: IO ()
printHelp = do
  putStrLn "prism-theme-generator - Formally verified color theme generation"
  putStrLn ""
  putStrLn "USAGE:"
  putStrLn "  prism-theme-generator generate"
  putStrLn "    Read ThemeConfig JSON from stdin, write variants to stdout"
  putStrLn ""
  putStrLn "  prism-theme-generator convert --from <space> --to <space> <color>"
  putStrLn "    Convert a color between color spaces"
  putStrLn "    Supported: srgb, oklch"
  putStrLn ""
  putStrLn "EXAMPLES:"
  putStrLn "  echo '{...}' | prism-theme-generator generate"
  putStrLn "  prism-theme-generator convert --from srgb --to oklch \"#ff5733\""
  putStrLn ""
  putStrLn "INPUT FORMAT (generate):"
  putStrLn "  {"
  putStrLn "    \"baseColor\": {\"hue\": 211, \"saturation\": 0.12, \"lightness\": 0.11},"
  putStrLn "    \"heroColor\": {\"hue\": 211, \"saturation\": 1.0, \"lightness\": 0.66},"
  putStrLn "    \"monitorType\": \"OLED\","
  putStrLn "    \"blackBalance\": 0.11,"
  putStrLn "    \"mode\": \"dark\""
  putStrLn "  }"
