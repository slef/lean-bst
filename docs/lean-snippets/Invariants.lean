theorem Rotate.size_eq (h : Rotate s t) : s.size = t.size
theorem Rotations.size_eq (h : Rotations s t k) : s.size = t.size
theorem Access.in_range (h : Access s t x k) : x < s.size
