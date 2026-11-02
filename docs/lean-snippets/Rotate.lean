inductive Rotate : Tree → Tree → Prop where
  | right {a b c : Tree} : Rotate (.node (.node a b) c) (.node a (.node b c))
  | left {a b c : Tree} : Rotate (.node a (.node b c)) (.node (.node a b) c)
  | inLeft {a b c : Tree} : Rotate a b → Rotate (.node a c) (.node b c)
  | inRight {a b c : Tree} : Rotate a b → Rotate (.node c a) (.node c b)
