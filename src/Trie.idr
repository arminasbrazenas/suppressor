module Trie

import Data.Vect

%default total

public export
data TrieLevel = Root | Node

public export
data Trie : TrieLevel -> Type where
  MkTrieRoot : (size : Nat) -> 
               (children : Vect size (Trie Node)) -> Trie Root
  MkTrieNode : (size : Nat) -> 
               (children : Vect size (Trie Node)) -> 
               (value : Char) -> 
               (isTerminal : Bool) -> Trie Node

export
size : Trie _ -> Nat
size (MkTrieRoot x _) = x
size (MkTrieNode x _ _ _) = x

export
children : (trie : Trie _) -> Vect (size trie) (Trie Node)
children (MkTrieRoot _ x) = x
children (MkTrieNode _ x _ _) = x

export
value : Trie Node -> Char
value (MkTrieNode _ _ x _) = x

export
isTerminal : Trie Node -> Bool
isTerminal (MkTrieNode _ _ _ x) = x

export
emptyTrie : Trie Root
emptyTrie = MkTrieRoot 0 []

export
buildNode : List Char -> Maybe (Trie Node)
buildNode [] = Nothing
buildNode [x] = Just $ MkTrieNode 0 [] x True
buildNode (x :: xs) = case buildNode xs of
  Nothing => Nothing
  Just child => Just $ MkTrieNode 1 [child] x False

export
findIndex : Char -> Vect n (Trie Node) -> Maybe (Fin n)
findIndex c [] = Nothing
findIndex c xs = findIndex (\x => value x == c) xs

insert'' : List Char -> Trie Node -> Trie Node
insert'' [] node = node
insert'' str@(c :: cs) node =
  case findIndex c (children node) of
    Nothing => case buildNode str of
      Nothing => node
      Just newChild => MkTrieNode ((size node) + 1)
                                  ((children node) ++ [newChild])
                                  (value node)
                                  (isTerminal node)
    Just idx => MkTrieNode (size node) 
                           (updateAt idx (\x => insert'' cs x) (children node))
                           (value node)
                           (isTerminal node)

insert' : List Char -> Trie Root -> Trie Root
insert' [] root = root
insert' str@(c :: cs) root = 
  case findIndex c (children root) of
    Nothing => case buildNode str of
      Nothing => root
      Just newNode => MkTrieRoot ((size root) + 1) 
                                 ((children root) ++ [newNode])
    Just idx => MkTrieRoot (size root) 
                           (updateAt idx (\x => insert'' cs x) (children root))

export
insert : String -> Trie Root -> Trie Root
insert str trie = insert' (unpack str) trie

lookup'' : List Char -> Trie Node -> Vect n (Trie Node) -> Maybe (Trie Node)
lookup'' [] parent _ = Just parent
lookup'' (_ :: _) parent [] = Nothing
lookup'' str@(c :: cs) parent (n :: ns) =
  if value n == c then 
    lookup'' cs n $ children n
  else 
    lookup'' str parent ns

lookup' : List Char -> Vect n (Trie Node) -> Maybe (Trie Node)
lookup' [] _ = Nothing
lookup' _ [] = Nothing
lookup' str@(c :: cs) (n :: ns) =
  if value n == c then 
    lookup'' cs n (children n)  
  else 
    lookup' str ns

export
lookup : List Char -> Trie _ -> Maybe (Trie Node)
lookup str root = lookup' str (children root)
