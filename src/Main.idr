module Main

import Data.Vect
import Data.List

-- %default total

record Trie a where
  constructor MkTrie
  value : a
  isTerminal : Bool
  children : List (Trie a)

lookupFarthest' : Eq a => Vect n a -> Trie a -> List (Trie a) -> Trie a
lookupFarthest' [] x _ = x
lookupFarthest' _ x [] = x
lookupFarthest' xxs@(x :: xs) y (z :: zs) = 
  if .value z == x
    then lookupFarthest' xs z (.children z)
    else lookupFarthest' xxs y zs

lookupFarthest : Eq a => Vect n a -> Trie a -> Trie a
lookupFarthest [] x = x
lookupFarthest x y = lookupFarthest' x y (.children y)

insert : Eq a => Vect n a -> Trie a -> Trie a

blacklist : List String
blacklist = ["yep", "nop"]

customBlacklist : List String
customBlacklist = ["add"]

together = union blacklist customBlacklist

el = find (\x => x == "nop") blacklist
