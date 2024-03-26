module Main

import System.REPL
import Data.String
import Data.Vect
import Decidable.Equality
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

addToBlacklist : String -> Language -> DataStore -> DataStore
addToBlacklist str lang store =
  case findIndex (\f => f .lang == lang) store .filters of
    Nothing => MkDataStore (store .size + 1) 
                           (store .filters ++ [MkFilter lang (insert (toLower str) emptyTrie)])
    Just idx => MkDataStore (store .size)
                            (updateAt idx (\f => MkFilter lang (insert (toLower str) f .blacklist)) store .filters)

plusSuccRightPlusOne : (n : Nat) -> (m : Nat) -> S (n + m) = n + (m + 1)
plusSuccRightPlusOne n m = 
  rewrite plusCommutative m 1 in
  rewrite plusSuccRightSucc n m in Refl

replaceWithChar' : {n : Nat} -> {m : Nat} -> Char -> Vect n Char -> Vect m Char -> Vect (n + m) Char
replaceWithChar' c [] acc = acc
replaceWithChar' {n = S k} {m} c (x :: xs) acc = rewrite plusSuccRightPlusOne k m in replaceWithChar' c xs (acc ++ [c])

replaceWithChar : {n : Nat} -> Char -> Vect n Char -> Vect n Char
replaceWithChar {n} c xs = rewrite sym $ plusZeroRightNeutral n in replaceWithChar' c xs []

parseProfanity : {n : Nat} -> {m : Nat} -> Vect n Char -> Vect m Char -> Trie Node -> Maybe ((p ** Vect p Char), (q ** Vect q Char))
parseProfanity {n = Z} {m} [] acc node = case isTerminal node of
  False => Nothing
  True => Just ((m ** acc), (0 ** []))
parseProfanity {n = S k} {m} xxs@(x :: xs) acc node = case isTerminal node of
  False => case lookup [toLower x] node of
    Nothing => Nothing
    Just childNode => parseProfanity xs (acc ++ [x]) childNode
  True => Just ((m ** acc), (S k ** xxs))

suppressProfanities' : {n : Nat} -> {m : Nat} -> Vect n Char -> Vect m Char -> Trie Root -> Nat -> Vect (n + m) Char
suppressProfanities' [] acc _ _ = acc
suppressProfanities' xs acc _ Z = xs ++ acc
suppressProfanities' {n = S k} {m} xxs@(x :: xs) acc root (S it) =
  case lookup [toLower x] root of
    Nothing => rewrite plusSuccRightPlusOne k m in suppressProfanities' xs (acc ++ [x]) root it
    Just node => case parseProfanity xs [x] node of
      Nothing => rewrite plusSuccRightPlusOne k m in suppressProfanities' xs (acc ++ [x]) root it
      Just ((profanityLen ** profanity), (restLen ** rest)) => case decEq (S (k + m)) (restLen + (m + profanityLen)) of
        Yes prf => rewrite prf in suppressProfanities' rest (acc ++ (replaceWithChar '*' profanity)) root it
        No _ => rewrite plusSuccRightPlusOne k m in suppressProfanities' xs (acc ++ [x]) root it -- should not happen; proof in parseProfanity function needed?

suppressProfanities : {n : Nat} -> Vect n Char -> Trie Root -> Vect n Char
suppressProfanities {n} xs root = rewrite sym $ plusZeroRightNeutral n in suppressProfanities' xs [] root (length xs)

some = insert "labas" emptyTrie
some2 = insert "labasasa" some
some3 = insert "labukas" some2
some4 = insert "antanas" some3

processInput : String -> String
processInput inp = (pack $ toList $ suppressProfanities (fromList $ unpack inp) some4) ++ "\n"

covering
main : IO ()
main = repl ">>> " processInput