inductive Rotate : Tree → Tree → Prop where
  | right : Rotate (.node (.node a b) c) (.node a (.node b c))
  | left : Rotate (.node a (.node b c)) (.node (.node a b) c)
  | inLeft : Rotate a b → Rotate (.node a c) (.node b c)
  | inRight : Rotate a b → Rotate (.node c a) (.node c b)
