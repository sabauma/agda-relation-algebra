{-# LANGUAGE OverloadedStrings #-}
module Database (dbDescription, runQuery, abort) where

import           Control.Monad    (liftM2)
import           Data.List        (intercalate)
import qualified Data.Text        as T
import           Database.SQLite3

escape :: T.Text -> T.Text
escape = T.replace "\n" "\\n"
       . T.replace "\"" "\\\""
       . T.replace "\\" "\\\\"

-- Convert data from an SQL database to a string representation that is
-- parsable by the recieving Agda program.
-- *  Numeric values are as expected.
-- *  Textual data is quoted.
-- *  Null values are given the representation 'NULL'.
mkDataStr :: SQLData -> String
mkDataStr (SQLInteger i) = show i
mkDataStr (SQLText t)    = "\"" ++ T.unpack (escape t) ++ "\""
mkDataStr SQLNull        = "NULL"
mkDataStr x              = error $ "Can only handle text and integer data: " ++ show x

-- Pull values from the statement until
getAllResults :: Statement -> IO [[String]]
getAllResults stmt = do
  res <- step stmt
  case res of
       Done -> return []
       Row  -> liftM2 (:) (map mkDataStr `fmap` columns stmt) (getAllResults stmt)

-- Execute a query and produce a single string which aggregates the results.
-- It might be easier to send a list of Strings back to Agda, but modifying
-- the parser to handle multiple results is not difficult at this point.
runQuery :: String -> IO String
runQuery str = do
  conn <- open "test.db"
  stmt <- prepare conn (T.pack str)
  cols <- getAllResults stmt
  finalize stmt >> close conn
  return $ unlines $ map (intercalate "|") cols

-- Run a specific query that gets the description of the table.
-- This description is also a table which will need to be parsed, but it
-- has a known format which can be determined from a schema.
dbDescription :: String -> IO String
dbDescription table = runQuery $ "PRAGMA table_info(" ++ table ++ ")"

-- A function for producing an error in the Agda code. This would be used
-- when the database description does not match what is expected from the
-- schema.
abort :: IO a
abort = error "Invalid database schema provided"
