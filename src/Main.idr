module Main

import Trie

%default total

some = insert "Labas" emptyTrie
some2 = insert "Labasasa" some
some3 = insert "Labasasas" some2
some4 = insert "Antanas" some3

prev = lookup "Lab" some4
next = case prev of
  Nothing => Nothing
  Just p => lookup "as" p

another = insert "Labas" emptyTrie
another2 = insert "Lazda" another
