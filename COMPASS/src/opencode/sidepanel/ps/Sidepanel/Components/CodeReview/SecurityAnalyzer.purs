{-|
Module      : Sidepanel.Components.CodeReview.SecurityAnalyzer
Description : Security vulnerability detection
Detects security vulnerabilities using pattern matching and AST analysis.
-}
module Sidepanel.Components.CodeReview.SecurityAnalyzer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.CodeReview.CodeReviewTypes
  ( CodeReviewIssue
  , SecurityVulnerability(..)
  , Severity(..)
  , IssueCategory(..)
  , Location
  , CodeFix
  )

-- | Analyze code for security vulnerabilities
analyzeSecurity :: String -> String -> Aff (Array CodeReviewIssue)
analyzeSecurity filePath content = do
  -- Run multiple security checks in parallel
  let sqlInjectionIssues = detectSQLInjection filePath content
  let xssIssues = detectXSS filePath content
  let commandInjectionIssues = detectCommandInjection filePath content
  let hardcodedSecretIssues = detectHardcodedSecrets filePath content
  let insecureDeserializationIssues = detectInsecureDeserialization filePath content
  
  pure $ sqlInjectionIssues <> xssIssues <> commandInjectionIssues <> 
         hardcodedSecretIssues <> insecureDeserializationIssues

-- | Detect SQL injection vulnerabilities
detectSQLInjection :: String -> String -> Array CodeReviewIssue
detectSQLInjection filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectSQLInjectionLine filePath lineIdx line) lines

-- | Detect SQL injection in a single line
detectSQLInjectionLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectSQLInjectionLine filePath lineIdx line = do
  -- Pattern: String interpolation in SQL queries
  -- Examples: `SELECT * FROM users WHERE id = ${userId}`
  --           `query = "SELECT * FROM " + tableName`
  
  let hasStringInterpolation = String.contains (String.Pattern "${") line ||
                                String.contains (String.Pattern "+") line
  
  let hasSQLKeywords = String.contains (String.Pattern "SELECT") line ||
                       String.contains (String.Pattern "INSERT") line ||
                       String.contains (String.Pattern "UPDATE") line ||
                       String.contains (String.Pattern "DELETE") line ||
                       String.contains (String.Pattern "WHERE") line
  
  if hasStringInterpolation && hasSQLKeywords then
    Just
      { severity: Critical
      , category: SecurityIssue
      , message: "Potential SQL injection vulnerability: User input directly concatenated into SQL query"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Use parameterized queries or prepared statements instead of string concatenation"
      , fix: Just
          { range:
              { start:
                  { file: filePath
                  , line: lineIdx + 1
                  , column: 0
                  , endLine: lineIdx + 1
                  , endColumn: 0
                  }
              , end:
                  { file: filePath
                  , line: lineIdx + 1
                  , column: 0
                  , endLine: lineIdx + 1
                  , endColumn: 0
                  }
              }
          , replacement: "-- Use parameterized query: db.query('SELECT * FROM users WHERE id = ?', [userId])"
          , description: "Replace string concatenation with parameterized query"
          , autoApplicable: false
          }
      , rule: "security/sql-injection"
      , confidence: 0.8
      }
  else
    Nothing

-- | Detect XSS vulnerabilities
detectXSS :: String -> String -> Array CodeReviewIssue
detectXSS filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectXSSLine filePath lineIdx line) lines

-- | Detect XSS in a single line
detectXSSLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectXSSLine filePath lineIdx line = do
  -- Pattern: User input directly inserted into HTML/DOM
  -- Examples: `element.innerHTML = userInput`
  --           `<div>{userInput}</div>`
  
  let hasInnerHTML = String.contains (String.Pattern "innerHTML") line ||
                     String.contains (String.Pattern "outerHTML") line
  
  let hasDangerouslySetInnerHTML = String.contains (String.Pattern "dangerouslySetInnerHTML") line
  
  let hasUnescapedInterpolation = String.contains (String.Pattern "{") line &&
                                   (String.contains (String.Pattern "userInput") line ||
                                    String.contains (String.Pattern "userData") line ||
                                    String.contains (String.Pattern "props.") line)
  
  if (hasInnerHTML || hasDangerouslySetInnerHTML || hasUnescapedInterpolation) then
    Just
      { severity: Major
      , category: SecurityIssue
      , message: "Potential XSS vulnerability: User input inserted into DOM without sanitization"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Sanitize user input before inserting into DOM, or use textContent instead of innerHTML"
      , fix: Nothing
      , rule: "security/xss"
      , confidence: 0.7
      }
  else
    Nothing

-- | Detect command injection vulnerabilities
detectCommandInjection :: String -> String -> Array CodeReviewIssue
detectCommandInjection filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectCommandInjectionLine filePath lineIdx line) lines

-- | Detect command injection in a single line
detectCommandInjectionLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectCommandInjectionLine filePath lineIdx line = do
  -- Pattern: User input in shell commands
  -- Examples: `exec(userInput)`
  --           `spawn('command', [userInput])`
  
  let hasExec = String.contains (String.Pattern "exec(") line ||
                String.contains (String.Pattern "execSync(") line ||
                String.contains (String.Pattern "spawn(") line ||
                String.contains (String.Pattern "system(") line
  
  let hasUserInput = String.contains (String.Pattern "userInput") line ||
                     String.contains (String.Pattern "userData") line ||
                     String.contains (String.Pattern "req.") line ||
                     String.contains (String.Pattern "params.") line
  
  if hasExec && hasUserInput then
    Just
      { severity: Critical
      , category: SecurityIssue
      , message: "Potential command injection vulnerability: User input used in shell command"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Validate and sanitize user input, or use parameterized command execution"
      , fix: Nothing
      , rule: "security/command-injection"
      , confidence: 0.9
      }
  else
    Nothing

-- | Detect hardcoded secrets
detectHardcodedSecrets :: String -> String -> Array CodeReviewIssue
detectHardcodedSecrets filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectHardcodedSecretLine filePath lineIdx line) lines

-- | Detect hardcoded secret in a single line
detectHardcodedSecretLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectHardcodedSecretLine filePath lineIdx line = do
  -- Pattern: Hardcoded API keys, passwords, tokens
  -- Examples: `apiKey = "sk-..."` (Starts with common prefixes)
  --           `password = "secret123"`
  --           `token = "Bearer ..."`
  
  let hasApiKey = String.contains (String.Pattern "apiKey") line ||
                  String.contains (String.Pattern "api_key") line ||
                  String.contains (String.Pattern "apikey") line
  
  let hasPassword = String.contains (String.Pattern "password") line ||
                    String.contains (String.Pattern "pwd") line ||
                    String.contains (String.Pattern "secret") line ||
                    String.contains (String.Pattern "token") line
  
  let hasHardcodedValue = String.contains (String.Pattern "= \"") line ||
                          String.contains (String.Pattern "= '") line ||
                          String.contains (String.Pattern "=\"") line ||
                          String.contains (String.Pattern "='") line
  
  -- Check for common secret patterns
  let hasSecretPattern = String.contains (String.Pattern "sk-") line ||
                         String.contains (String.Pattern "Bearer ") line ||
                         String.contains (String.Pattern "ghp_") line ||
                         String.contains (String.Pattern "xoxb-") line
  
  if (hasApiKey || hasPassword) && hasHardcodedValue && hasSecretPattern then
    Just
      { severity: Critical
      , category: SecurityIssue
      , message: "Hardcoded secret detected: API keys, passwords, or tokens should not be committed to code"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Use environment variables or a secrets management system instead"
      , fix: Nothing
      , rule: "security/hardcoded-secret"
      , confidence: 0.95
      }
  else
    Nothing

-- | Detect insecure deserialization
detectInsecureDeserialization :: String -> String -> Array CodeReviewIssue
detectInsecureDeserialization filePath content = do
  let lines = String.split (String.Pattern "\n") content
  
  Array.mapMaybeWithIndex (\lineIdx line -> detectInsecureDeserializationLine filePath lineIdx line) lines

-- | Detect insecure deserialization in a single line
detectInsecureDeserializationLine :: String -> Int -> String -> Maybe CodeReviewIssue
detectInsecureDeserializationLine filePath lineIdx line = do
  -- Pattern: Deserialization of untrusted data
  -- Examples: `JSON.parse(userInput)` without validation
  --           `eval(userInput)`
  --           `pickle.loads(userInput)` (Python)
  
  let hasDeserialization = String.contains (String.Pattern "JSON.parse(") line ||
                           String.contains (String.Pattern "eval(") line ||
                           String.contains (String.Pattern "deserialize") line ||
                           String.contains (String.Pattern "unserialize") line
  
  let hasUserInput = String.contains (String.Pattern "userInput") line ||
                     String.contains (String.Pattern "req.body") line ||
                     String.contains (String.Pattern "params.") line
  
  if hasDeserialization && hasUserInput then
    Just
      { severity: Major
      , category: SecurityIssue
      , message: "Potential insecure deserialization: Untrusted data deserialized without validation"
      , location:
          { file: filePath
          , line: lineIdx + 1
          , column: 0
          , endLine: lineIdx + 1
          , endColumn: String.length line
          }
      , suggestion: Just "Validate and sanitize input before deserialization, or use a safe deserialization library"
      , fix: Nothing
      , rule: "security/insecure-deserialization"
      , confidence: 0.75
      }
  else
    Nothing
