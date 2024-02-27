module Main

import Data.Vect
import Data.List

%default total

data TrieLevel = Root | Node

data Trie : TrieLevel -> Type where
  MkTrieRoot : (size : Nat) -> 
               (children : Vect size (Trie Node)) -> Trie Root
  MkTrieNode : (size : Nat) -> 
               (children : Vect size (Trie Node)) -> 
               (value : Char) -> 
               (isTerminal : Bool) -> Trie Node

size : Trie _ -> Nat
size (MkTrieRoot x _) = x
size (MkTrieNode x _ _ _) = x

children : (trie : Trie _) -> Vect (size trie) (Trie Node)
children (MkTrieRoot _ x) = x
children (MkTrieNode _ x _ _) = x

value : Trie Node -> Char
value (MkTrieNode _ _ x _) = x

isTerminal : Trie Node -> Bool
isTerminal (MkTrieNode _ _ _ x) = x

buildRoot : Trie Root
buildRoot = MkTrieRoot 0 []

buildNode : List Char -> Maybe (Trie Node)
buildNode [] = Nothing
buildNode [x] = Just $ MkTrieNode 0 [] x True
buildNode (x :: xs) = case buildNode xs of
  Nothing => Nothing
  Just child => Just $ MkTrieNode 1 [child] x False

findNodeIndex : Char -> Vect n (Trie Node) -> Maybe (Fin n)
findNodeIndex c [] = Nothing
findNodeIndex c xs = findIndex (\x => value x == c) xs

insertAtNode : List Char -> Trie Node -> Trie Node
insertAtNode [] node = node
insertAtNode str@(c :: cs) node = 
  case findNodeIndex c (children node) of
    Nothing => case buildNode str of
      Nothing => node
      Just newChild => MkTrieNode 
                        ((size node) + 1)
                        ((children node) ++ [newChild])
                        (value node)
                        (isTerminal node)
    Just idx => MkTrieNode
                  (size node) 
                  (updateAt idx (\x => insertAtNode cs x) (children node))
                  (value node)
                  (isTerminal node)

insertAtRoot : List Char -> Trie Root -> Trie Root
insertAtRoot [] root = root
insertAtRoot str@(c :: cs) root = 
  case findNodeIndex c (children root) of
    Nothing => case buildNode str of
      Nothing => root
      Just newNode => MkTrieRoot 
                        ((size root) + 1) 
                        ((children root) ++ [newNode])
    Just idx => MkTrieRoot 
                  (size root) 
                  (updateAt idx (\x => insertAtNode cs x) (children root))

insert : String -> Trie Root -> Trie Root
insert str trie = insertAtRoot (unpack str) trie

lookupNode : List Char -> Trie Node -> Vect n (Trie Node) -> Maybe (Trie Node)
lookupNode [] parent _ = Just parent
lookupNode (_ :: _) parent [] = Nothing
lookupNode str@(c :: cs) parent (n :: ns) =
  if value n == c
    then lookupNode cs n $ children n
    else lookupNode str parent ns

lookupNodes : List Char -> Vect n (Trie Node) -> Maybe (Trie Node)
lookupNodes [] _ = Nothing
lookupNodes _ [] = Nothing
lookupNodes (c :: cs) (n :: ns) =
  if value n == c
    then lookupNode cs n (children n)  
    else lookupNodes cs ns

lookup : String -> Trie _ -> Maybe (Trie Node)
lookup str root = lookupNodes (unpack str) (children root)

some = insert "Labas" buildRoot
some2 = insert "Labasasa" some
some3 = insert "Labasasas" some2
some4 = insert "Antanas" some3

prev = lookup "Lab" some4
next = case prev of
  Nothing => Nothing
  Just p => lookup "as" p