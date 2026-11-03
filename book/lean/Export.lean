import RotationBST
import Lean

/-!
# Book export

Run from the Lean project root with

    BOOK_NAMES=names.txt BOOK_OUT=consts.json BOOK_VECTORS=vectors.json \
      lake env lean book/lean/Export.lean

`BOOK_NAMES` lists one constant per line. For each, the script records the
kind, the signature as the editor hover would print it, the docstring, the
owning module and, for library declarations, the axioms it depends on.

`BOOK_VECTORS` receives results of the executable library functions on small
inputs. The test suite compares the book's JavaScript ports against them, so
the visualizers are checked against the Lean definitions.
-/

open Lean Meta Elab Command

namespace BookExport

def kindOf (env : Environment) (n : Name) (inst : Bool) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "recursor"
  | .ctorInfo _ => "constructor"
  | .inductInfo _ =>
      if isClass env n then "class"
      else if isStructure env n then "structure" else "inductive"
  | .defnInfo _ =>
      if inst then "instance"
      else if (getStructureInfo? env n.getPrefix).any (·.fieldNames.contains n.getString!.toName)
        then "field" else "def"

def exportConst (n : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let some info := env.find? n | return none
  let sig ← try
      pure ((← PrettyPrinter.ppSignature n).fmt.pretty 100)
    catch _ => pure s!"{n}"
  let doc ← findDocString? env n
  let mod := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => ""
  let isLocal := (`RotationBST).isPrefixOf mod.toName
  let axioms ← if isLocal then
      pure <| some ((← collectAxioms n).map (·.toString)).toList
    else pure none
  -- Declaration ranges as LSP positions (zero-based lines, UTF-16 columns),
  -- like the .ilean files; used when an .ilean file omits a declaration.
  let rangeField ← match ← findDeclarationRanges? n with
    | some r => pure [("range", toJson [r.range.pos.line - 1, r.range.charUtf16,
        r.range.endPos.line - 1, r.range.endCharUtf16, r.selectionRange.pos.line - 1,
        r.selectionRange.charUtf16, r.selectionRange.endPos.line - 1,
        r.selectionRange.endCharUtf16])]
    | none => pure []
  let base := [("name", Json.str n.toString), ("kind", Json.str (kindOf env n (← isInstance n) info)),
    ("sig", Json.str sig), ("module", Json.str mod)] ++ rangeField
  let docField := match doc with | some d => [("doc", Json.str d)] | none => []
  let axField := match axioms with
    | some as => [("axioms", Json.arr (as.map Json.str).toArray)]
    | none => []
  return some (Json.mkObj (base ++ docField ++ axField))

/-! ## Test vectors for the JavaScript ports -/

open RotationBST

def treeJson : Tree → Json
  | .nil => Json.null
  | .node l r => Json.arr #[treeJson l, treeJson r]

def frameJson : Pointer.Frame → Json
  | .left r => Json.mkObj [("side", "left"), ("tree", treeJson r)]
  | .right l => Json.mkObj [("side", "right"), ("tree", treeJson l)]

/-- All shapes with exactly `n` nodes. -/
partial def shapes : Nat → List Tree
  | 0 => [.nil]
  | n + 1 => (List.range (n + 1)).flatMap fun i =>
      (shapes i).flatMap fun l => (shapes (n - i)).map fun r => .node l r

/-- A deterministic pseudo-random shape, for larger tests. -/
def randomTree (seed n : Nat) : Tree := Id.run do
  -- Insert keys in a pseudo-random order into an unbalanced BST, then
  -- forget the keys. Every shape is reachable this way.
  let mut keys : Array Nat := #[]
  let mut s := seed
  for i in [0:n] do
    keys := keys.push i
  for i in [0:n] do
    s := (s * 1103515245 + 12345) % 2147483648
    let j := i + s % (n - i)
    keys := keys.swapIfInBounds i j
  let rec ins : List Nat → Nat → Tree
    | [], _ => .nil
    | _, 0 => .nil
    | k :: ks, fuel + 1 =>
        let left := ks.filter (· < k)
        let right := ks.filter (· > k)
        .node (ins left fuel) (ins right fuel)
  return ins keys.toList (n + 1)

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def randomSeq (seed n len : Nat) : List Nat := Id.run do
  let mut s := seed
  let mut out := #[]
  for _ in [0:len] do
    s := lcg s
    out := out.push (s / 7 % n)
  return out.toList


/-! ### Vectors for the later parts: move-to-root, geometry, Wilber/Tango, split trees -/

def moveToRootVectors : Array Json := Id.run do
  let trees := (List.range 6).flatMap shapes ++ (List.range 6).map fun i => randomTree (i + 40) (9 + 2 * i)
  let mut out := #[]
  for t in trees do
    for x in List.range t.size do
      let (u, k) := moveToRoot t x
      out := out.push <| Json.mkObj [("tree", treeJson t), ("x", toJson x),
        ("result", treeJson u), ("cost", toJson k)]
  return out

/-- Points of `P` with key `< n` and time `< m`, sorted by time then key. -/
def pointsJson (P : Finset Geometric.Point) (n m : Nat) : Json :=
  toJson <| (List.range m).flatMap fun time =>
    ((List.range n).filter fun x => decide ((x, time) ∈ P)).map fun x => [x, time]

def geometricVectors : Array Json := Id.run do
  let mut out := #[]
  for i in [0:14] do
    let n := 3 + i % 6
    let len := 4 + i % 7
    let xs := if i % 5 == 0 then List.range n else randomSeq (31 * i + 5) n len
    let P := Geometric.fill Geometric.greedySweep 0 ∅ xs
    out := out.push <| Json.mkObj [("n", toJson n), ("requests", toJson xs),
      ("points", pointsJson P n xs.length),
      ("rowCost", toJson (Geometric.rowCost Geometric.greedySweep 0 ∅ xs)),
      ("satisfied", toJson (decide (Geometric.ASS P)))]
  return out

/-- Small pseudo-random point sets, to test an arboral-satisfaction checker. -/
def assVectors : Array Json := Id.run do
  let mut out := #[]
  let mut s := 17
  for i in [0:40] do
    let n := 3 + i % 4
    let m := 3 + i % 3
    let mut P : Finset Geometric.Point := ∅
    for x in List.range n do
      for time in List.range m do
        s := lcg s
        if s / 13 % 3 == 0 then P := insert (x, time) P
    out := out.push <| Json.mkObj [("n", toJson n), ("m", toJson m),
      ("points", pointsJson P n m), ("satisfied", toJson (decide (Geometric.ASS P)))]
  return out

def referenceVectors : Array Json := Id.run do
  let mut out := #[]
  for i in [0:16] do
    let n := 3 + i
    let t := if i % 3 == 0 then Tango.balanced n else randomTree (200 + i) n
    let xs := if i % 4 == 1 then List.range n else randomSeq (11 * i + 7) n (2 * n)
    let prefixes := (List.range (xs.length + 1)).map fun j => Tango.preferredPaths t (xs.take j)
    out := out.push <| Json.mkObj [("tree", treeJson t), ("requests", toJson xs),
      ("interleave", toJson (Wilber.interleave t xs)),
      ("absoluteInterleave", toJson (Wilber.absoluteInterleave t 0 xs)),
      ("changes", toJson ((List.range xs.length).map fun j => Tango.changes t (xs.take j) xs[j]!)),
      ("preferenceChanges", toJson (Tango.preferenceChanges t xs)),
      ("initializations", toJson (Tango.initializations t xs)),
      ("preferredPaths", toJson prefixes),
      ("transitionKeys", toJson (Wilber.transitionKeys t 0 t)),
      ("height", toJson (Tango.height t))]
  for n in List.range 12 do
    out := out.push <| Json.mkObj [("balanced", toJson n), ("tree", treeJson (Tango.balanced n))]
  return out

open Geometric.Split in
def multiwayJson : Multiway → Json
  | .nil => Json.null
  | .two a b => Json.arr #[multiwayJson a, multiwayJson b]
  | .three a b c => Json.arr #[multiwayJson a, multiwayJson b, multiwayJson c]
  | .four a b c d => Json.arr #[multiwayJson a, multiwayJson b, multiwayJson c, multiwayJson d]

open Geometric.Split in
/-- Balanced 2–3–4 trees of height `h`, with a pseudo-random choice of degrees. -/
def randomMultiway (seed : Nat) : Nat → Multiway
  | 0 => .nil
  | h + 1 =>
      let s₁ := lcg seed
      let s₂ := lcg s₁
      let s₃ := lcg s₂
      let s₄ := lcg s₃
      match seed / 7 % 3 with
      | 0 => .two (randomMultiway s₁ h) (randomMultiway s₂ h)
      | 1 => .three (randomMultiway s₁ h) (randomMultiway s₂ h) (randomMultiway s₃ h)
      | _ => .four (randomMultiway s₁ h) (randomMultiway s₂ h) (randomMultiway s₃ h)
          (randomMultiway s₄ h)

open Geometric.Split Geometric.Split.Multiway.Finger in
def multiwayVectors : Array Json := Id.run do
  let mut out := #[]
  for i in [0:30] do
    let t := randomMultiway (i * 977 + 3) (1 + i % 4)
    let v := binaryView t
    out := out.push <| Json.mkObj [("tree", multiwayJson t), ("size", toJson t.size),
      ("binary", treeJson t.binary), ("view", treeJson v.tree),
      ("spine", toJson v.spine.length), ("viewCost", toJson (viewCost t)),
      ("searchLevels", toJson ((List.range t.size).map (searchLevels t))),
      ("nearSearchLevels", toJson ((List.range t.size).map (nearSearchLevels t))),
      ("prepareLeft", match Multiway.prepareLeft t with | (u, k) => Json.arr #[multiwayJson u, toJson k]),
      ("prepareRight", match Multiway.prepareRight t with | (u, k) => Json.arr #[multiwayJson u, toJson k]),
      ("mirror", multiwayJson (mirror t))]
  for h in List.range 6 do
    out := out.push <| Json.mkObj [("totalChargeTree", treeJson (Tango.balanced (2 ^ h + h))),
      ("totalCharge", toJson (totalCharge (Tango.balanced (2 ^ h + h))))]
  return out

def vectors : Json := Id.run do
  let small := (List.range 7).flatMap shapes
  let large := (List.range 12).map fun i => randomTree (i + 1) (8 + 3 * i)
  let trees := small ++ large
  let mut splay := #[]
  let mut updates := #[]
  for t in trees do
    for x in List.range t.size do
      let c := Splay.locate t x
      let (u, k) := Splay.run t x
      splay := splay.push <| Json.mkObj [("tree", treeJson t), ("x", toJson x),
        ("context", Json.arr (c.context.map frameJson).toArray),
        ("result", treeJson u), ("cost", toJson k),
        ("depth", toJson (StaticTree.depth t x))]
    if t.size ≤ 5 then
      for k in List.range (t.size + 1) do
        let s := Splay.Updates.split t k
        let (i, ic) := Splay.Updates.insert t k
        updates := updates.push <| Json.mkObj [("op", "split"), ("tree", treeJson t),
          ("k", toJson k), ("left", treeJson s.left), ("right", treeJson s.right),
          ("cost", toJson s.cost)]
        updates := updates.push <| Json.mkObj [("op", "insert"), ("tree", treeJson t),
          ("k", toJson k), ("result", treeJson i), ("cost", toJson ic)]
      for x in List.range t.size do
        let (d, dc) := Splay.Updates.delete t x
        updates := updates.push <| Json.mkObj [("op", "delete"), ("tree", treeJson t),
          ("k", toJson x), ("result", treeJson d), ("cost", toJson dc)]
  for l in (List.range 4).flatMap shapes do
    for r in (List.range 3).flatMap shapes do
      let (j, jc) := Splay.Updates.join l r
      updates := updates.push <| Json.mkObj [("op", "join"), ("left", treeJson l),
        ("right", treeJson r), ("result", treeJson j), ("cost", toJson jc)]
  let mut sequences := #[]
  for i in [0:16] do
    let n := 3 + i
    let t := randomTree (100 + i) n
    let xs := if i % 4 == 0 then List.range n else randomSeq (7 * i + 3) n (2 * n + i)
    let ws := (List.range xs.length).map fun j =>
      workingSetNumber n (xs.take j) xs[j]!
    sequences := sequences.push <| Json.mkObj [("tree", treeJson t), ("n", toJson n),
      ("requests", toJson xs), ("final", treeJson (Splay.algorithm.runFrom [] t xs).1),
      ("cost", toJson (Splay.algorithm.cost t xs)),
      ("totalCost", toJson (Splay.algorithm.totalCost t xs)),
      ("workingSetNumbers", toJson ws),
      ("workingSetSum", toJson (workingSetSum n [] xs)),
      ("staticTreeCost", toJson (StaticTree.cost t xs))]
  return Json.mkObj [("splay", Json.arr splay), ("updates", Json.arr updates),
    ("sequences", Json.arr sequences), ("moveToRoot", Json.arr moveToRootVectors),
    ("geometric", Json.arr geometricVectors), ("ass", Json.arr assVectors),
    ("reference", Json.arr referenceVectors), ("multiway", Json.arr multiwayVectors)]

end BookExport

-- Print signatures as a reader inside the library namespace would see them.
open BookExport RotationBST in
run_meta do
  let some namesPath ← IO.getEnv "BOOK_NAMES" | throwError "BOOK_NAMES is not set"
  let some outPath ← IO.getEnv "BOOK_OUT" | throwError "BOOK_OUT is not set"
  let names := (← IO.FS.lines namesPath).filter (· ≠ "")
  let mut out : Array Json := #[]
  let mut missing : Array String := #[]
  for line in names do
    match ← exportConst line.toName with
    | some j => out := out.push j
    | none => missing := missing.push line
  IO.FS.writeFile outPath (Json.mkObj [("consts", Json.arr out),
    ("missing", toJson missing)]).compress
  if let some vectorsPath ← IO.getEnv "BOOK_VECTORS" then
    IO.FS.writeFile vectorsPath vectors.compress
