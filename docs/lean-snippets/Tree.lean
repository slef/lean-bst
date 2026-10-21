inductive Tree where
  | nil
  | node (left right : Tree)
  deriving DecidableEq, Repr
