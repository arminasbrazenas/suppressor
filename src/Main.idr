module Main

import Data.Vect
import Data.List

-- %default total

record TrieNode where
  constructor MkTrieNode
  children : List TrieNode
  value : Char
  isTerminal : Bool

record TrieRoot where
  constructor MkTrieRoot
  children : List TrieNode

lookupNode : List Char -> TrieNode -> List TrieNode -> Maybe TrieNode
lookupNode [] parent _ = Just parent
lookupNode _ parent [] = Nothing 
lookupNode xxs@(x :: xs) parent (y :: ys) =
  if .value y == x
    then lookupNode xs y $ .children y
    else lookupNode xxs parent ys

lookupNodes : List Char -> List TrieNode -> Maybe TrieNode
lookupNodes [] _ = Nothing
lookupNodes _ [] = Nothing
lookupNodes xxs@(x :: xs) (y :: ys) =
  if .value y == x
    then case lookupNode xs y $ .children y of
      Nothing => lookupNodes xs ys
      Just a => Just a
    else lookupNodes xxs ys
  
lookup : String -> TrieRoot -> Maybe TrieNode
lookup str root = lookupNodes (unpack str) (.children root)

createNode : List Char -> Maybe TrieNode
createNode [] = Nothing
createNode [x] = Just $ MkTrieNode [] x True
createNode (x :: xs) = case createNode xs of
  Nothing => Nothing
  Just child => Just $ MkTrieNode [child] x False

insert' : List Char -> List TrieNode -> List TrieNode -> List TrieNode
insert' [] [] acc = acc
insert' [] ys acc = acc ++ ys
insert' xs [] acc = case createNode xs of
  Nothing => acc
  Just node => acc ++ [node]
insert' xs@[x] (y :: ys) acc =
  if x == .value y
    then acc ++ [MkTrieNode (.children y) (.value y) True] ++ ys
    else insert' xs ys $ acc ++ [y]
insert' xxs@(x :: xs) (y :: ys) acc = 
  if x == .value y
    then acc ++ [MkTrieNode (insert' xs (.children y) []) (.value y) (.isTerminal y)] ++ ys
    else insert' xxs ys $ acc ++ [y]

insert : String -> TrieRoot -> TrieRoot
insert str root = MkTrieRoot $ insert' (unpack str) (.children root) []

emptyRoot : TrieRoot
emptyRoot = MkTrieRoot []

some = insert "Labas" emptyRoot
some2 = insert "Labasasa" some
some3 = insert "Antanas" some2
found = lookup "Antan" some3