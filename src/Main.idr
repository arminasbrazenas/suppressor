module Main

import System.REPL
import Data.String
import Data.Vect
import Trie

%default total

data Language = EN

Eq Language where
  EN == EN = True

record Filter where
  constructor MkFilter
  lang : Language
  blacklist : Trie Root

record DataStore where
  constructor MkDataStore
  size : Nat
  filters : Vect size Filter

record ProfanityResult where
  constructor MkProfanityResult
  parsed : List Char
  profanity : Maybe (List Char)
  rest : List Char

addToBlacklist : String -> Language -> DataStore -> DataStore
addToBlacklist str lang store = 
  case findIndex (\f => f .lang == lang) store .filters of
    Nothing => MkDataStore (store .size + 1) 
                           (store .filters ++ [MkFilter lang (insert (toLower str) emptyTrie)])
    Just idx => MkDataStore (store .size)
                            (updateAt idx (\f => MkFilter lang (insert (toLower str) f .blacklist)) store .filters)

findProfanity' : List Char -> Trie Node -> List Char -> Maybe (List Char)
findProfanity' [] node parsed =
  if isTerminal node then
    Just parsed
  else
    Nothing
findProfanity' str@(c :: cs) node parsed = 
  if isTerminal node then
    Just parsed
  else 
    case lookup [toLower c] node of
      Nothing => Nothing
      Just nextNode => findProfanity' cs nextNode (parsed ++ [c])

findProfanity : List Char -> Trie Root -> List Char -> ProfanityResult
findProfanity [] _ parsed = MkProfanityResult parsed Nothing []
findProfanity (c :: cs) root parsed = 
  case lookup [toLower c] root of
    Nothing => findProfanity cs root (parsed ++ [c])
    Just node => case findProfanity' cs node [] of
      Nothing => findProfanity cs root (parsed ++ [c])
      Just profanity => MkProfanityResult parsed 
                                          (Just ([c] ++ profanity)) 
                                          (drop (length profanity) cs)

exchange : Char -> List Char -> List Char
exchange _ [] = []
exchange c (x :: xs) = [c] ++ exchange c xs

suppressProfanities' : List Char -> Trie Root -> List Char -> Nat -> List Char
suppressProfanities' _ _ _ Z = []
suppressProfanities' str root parsed (S timeout) = 
  let
    res = findProfanity str root []
  in
    case res .profanity of
      Nothing => parsed ++ res .parsed
      Just prof => suppressProfanities' (res .rest) 
                                        root 
                                        (parsed ++ res .parsed ++ exchange '*' prof) 
                                        timeout

suppressProfanities : String -> Trie Root -> String
suppressProfanities str root = pack $ suppressProfanities' (unpack str) root [] (length str)

containsProfanities : String -> Trie Root -> Bool
containsProfanities str root =
  let
    res = findProfanity (unpack str) root []
  in
    case res .profanity of
      Nothing => False
      Just _ => True

some = insert "labas" emptyTrie
some2 = insert "labasasa" some
some3 = insert "labukas" some2
some4 = insert "antanas" some3

processInput : String -> String -> Maybe (String, String)
processInput str str1 = ?processInput_rhs

covering
main : IO ()
main = replWith "" ">>> " processInput