import D2RelationGap.InsertionTraceUpdate
import D2RelationGap.MoveSchedule

/-!
Dispatch the existing contextual Local operations, including arbitrary nested symmetry,
into constructed source updates. OpenAI, "A Counterexample to Wall's D(2) Problem"
(October 6, 2026), openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. No source exactness, source nullity or geometric adequacy is assumed.
-/
noncomputable section
namespace D2RelationGap.LocalTraceUpdate
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops SourceRefinement
open TriangleAttachment StutterTrace MoveSchedule SimplicialImages
universe u w
variable {V : Type u} {W : Type w} [LinearOrder V] [LinearOrder W]

/-- A constructed source embedding and actual source moves, with literal normalized trace.
The record is an output of the primitive dispatcher, never an input adequacy oracle. -/
structure Update {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b) (q : Path B (f a) (f b)) {budget : ℕ} where
  Ambient : Type u
  [order : LinearOrder Ambient]
  complex : PreAbstractSimplicialComplex Ambient
  embedding : V → Ambient
  injective : Function.Injective embedding
  embedding_face : A.map embedding ≤ complex
  labels : Ambient → W
  face_map : complex.map labels ≤ B
  labels_old : ∀ x, labels (embedding x) = f x
  upper : Path complex (embedding a) (embedding b)
  moves : Moves (mapPath embedding embedding_face p) upper
  trace : vertices (imageTrace labels face_map upper) = vertices (StutterTrace.normalize q)
  finite : Finite (Vertex A) → Finite (Vertex complex)
  count : Finite (Vertex A) → Nat.card (Vertex complex) ≤ Nat.card (Vertex A) + budget
  dimension : AtMostTwo A → AtMostTwo complex
  paths : ∀ (r : Vertex A), (∀ x : Vertex A, Path A r.val x.val) →
    ∀ x : Vertex complex, Path complex (embedding r.val) x.val
  span : ∀ {r : V} (g : Path A r r),
    CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g) →
    CycleSpan complex (PathChains.chain (PathChains.trivialTransport complex)
      (mapPath embedding embedding_face g))
  retained_value : ∀ {K : Type} [Field K] (tau : Transport (K := K) B)
    {i j : V} (g : Path A i j),
    value tau (mapPath labels face_map (mapPath embedding embedding_face g)) =
      value tau (mapPath f hf g)

attribute [instance] Update.order

/-- Package a checked deletion: its embedding is literally the identity. -/
def ofDeletion {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b) (q : Path B (f a) (f b))
    (s : TriangleTraceUpdate.Deletion f p q) : Update f hf p q (budget := 1) where
  Ambient := V
  order := inferInstance
  complex := s.complex
  embedding := id
  injective := Function.injective_id
  embedding_face := identity_face_map s.inclusion
  labels := f
  face_map := s.face_map
  labels_old _ := rfl
  upper := s.upper
  moves := s.moves
  trace := congrArg vertices s.realizes
  finite h := by let := h; exact TriangleTraceUpdate.source_finite f p q s
  count _ := by rw [TriangleTraceUpdate.source_count f p q s]; omega
  dimension := s.dimension
  paths := TriangleTraceUpdate.sourcePaths f p q s
  span := s.span
  retained_value tau _ _ g := TriangleTraceUpdate.retained_value f hf tau p q s g

/-- Package a checked insertion: its embedding is the injective old tag. -/
def ofInsertion {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b) (q : Path B (f a) (f b))
    (label : W) (s : InsertionTraceUpdate.Insertion f p q label) : Update f hf p q (budget := 1) where
  Ambient := SourceExpansion.Ambient V
  order := inferInstance
  complex := SourceExpansion.expansion A s.src s.dst
  embedding := SourceExpansion.old
  injective := by intro x y h; exact congrArg (fun z => (ofLex z).2) h
  embedding_face := SourceExpansion.old_face A s.src s.dst
  labels := SourceExpansion.extend f label
  face_map := s.face_map
  labels_old _ := rfl
  upper := s.upper
  moves := s.moves
  trace := congrArg vertices s.realizes
  finite h := by let := h; exact InsertionTraceUpdate.source_finite f p q label s
  count h := by let := h; rw [InsertionTraceUpdate.source_count f p q label s]
  dimension := InsertionTraceUpdate.source_dimension f p q label s
  paths := InsertionTraceUpdate.sourcePaths f p q label s
  span := InsertionTraceUpdate.source_span f p q label s
  retained_value tau _ _ g := InsertionTraceUpdate.retained_value f hf tau p q label s g

/-- Only the symmetry wrapper is recursive in a local operation. -/
def symmetryDepth {B : PreAbstractSimplicialComplex W} {x y : W}
    {t q : Path B x y} : Local t q → ℕ
  | .stutter _ _ _ => 0
  | .backtrack _ _ _ => 0
  | .triangle _ _ _ => 0
  | .symm m => symmetryDepth m + 1

/-- Simultaneous forward/reverse dispatch makes nested symmetry swap actual constructors. -/
def dispatchBoth {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} {t q : Path B (f a) (f b)} (m : Local t q) :
    ((p : Path A a b) → Realizes f hf p t → Update f hf p q (budget := 1)) ×
    ((p : Path A a b) → Realizes f hf p q → Update f hf p t (budget := 1)) := by
  cases m with
  | stutter pre hu post =>
    exact ⟨fun p h => ofDeletion f hf p _ (TriangleTraceUpdate.deleteStutter f hf p _ hu pre post h),
      fun p h => ofInsertion f hf p _ _ (InsertionTraceUpdate.insertStutter f hf p _ hu pre post h)⟩
  | backtrack pre huv post =>
    exact ⟨fun p h => ofDeletion f hf p _ (TriangleTraceUpdate.deleteBacktrack f hf p _ _ huv pre post h),
      fun p h => ofInsertion f hf p _ _ (InsertionTraceUpdate.insertBacktrack f hf p _ _ huv pre post h)⟩
  | triangle pre ht post =>
    exact ⟨fun p h => ofDeletion f hf p _ (TriangleTraceUpdate.deleteContext f hf p _ _ _ ht pre post h),
      fun p h => ofInsertion f hf p _ _ (InsertionTraceUpdate.insertContext f hf p _ _ _ ht pre post h)⟩
  | symm m =>
    let ih := dispatchBoth f hf m
    exact ⟨ih.2,ih.1⟩
termination_by symmetryDepth m
decreasing_by
  subst_vars
  simp_all [symmetryDepth]

/-- Endpoint transport changes no vertex in a target path. -/
def rebase {B : PreAbstractSimplicialComplex W} {x y x' y' : W}
    (ex : x' = x) (ey : y' = y) (p : Path B x y) : Path B x' y' := by
  subst x'; subst y'; exact p

theorem vertices_rebase {B : PreAbstractSimplicialComplex W} {x y x' y' : W}
    (ex : x' = x) (ey : y' = y) (p : Path B x y) : vertices (rebase ex ey p) = vertices p := by
  subst x'; subst y'; rfl

theorem normalize_rebase {B : PreAbstractSimplicialComplex W} {x y x' y' : W}
    (ex : x' = x) (ey : y' = y) (p : Path B x y) :
    vertices (StutterTrace.normalize (rebase ex ey p)) = vertices (StutterTrace.normalize p) := by
  subst x'; subst y'; rfl

/-- The computed trace is literal Realizes after the proved endpoint equations. -/
theorem realizes {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b) (q : Path B (f a) (f b))
    {n : ℕ} (s : Update f hf p q (budget := n)) :
    Realizes s.labels s.face_map s.upper (rebase (s.labels_old a) (s.labels_old b) q) := by
  apply vertices_injective
  exact s.trace.trans (normalize_rebase (s.labels_old a) (s.labels_old b) q).symm

/-- Ordinary composition of actual face maps, independent of order or injectivity. -/
theorem face_comp {X Y Z : Type*} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
    {A : PreAbstractSimplicialComplex X} {C : PreAbstractSimplicialComplex Y}
    {D : PreAbstractSimplicialComplex Z} (i : X → Y) (hi : A.map i ≤ C) (j : Y → Z) (hj : C.map j ≤ D) :
    A.map (j ∘ i) ≤ D := by
  rintro s ⟨t,ht,rfl⟩
  change t.image (j ∘ i) ∈ D
  rw [← Finset.image_image]
  exact image_mem j hj _ (image_mem i hi t ht)

theorem path_comp {X Y Z : Type*} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
    {A : PreAbstractSimplicialComplex X} {C : PreAbstractSimplicialComplex Y}
    {D : PreAbstractSimplicialComplex Z} (i : X → Y) (hi : A.map i ≤ C) (j : Y → Z) (hj : C.map j ≤ D)
    {a b : X} (p : Path A a b) :
    mapPath (j ∘ i) (face_comp i hi j hj) p = mapPath j hj (mapPath i hi p) := by
  induction p with
  | refl => rfl
  | cons h p ih => exact congrArg (Path.cons _) ih

theorem path_identity {A : PreAbstractSimplicialComplex V} {a b : V} (p : Path A a b) :
    mapPath id (identity_face_map (le_refl A)) p = p := by
  induction p with
  | refl => rfl
  | cons h p ih => exact congrArg (Path.cons _) ih

/-- Zero-step history retains the supplied source and trace. -/
def unchanged {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b) (q : Path B (f a) (f b))
    (h : Realizes f hf p q) : Update f hf p q (budget := 0) where
  Ambient := V
  order := inferInstance
  complex := A
  embedding := id
  injective := Function.injective_id
  embedding_face := identity_face_map (le_refl A)
  labels := f
  face_map := hf
  labels_old _ := rfl
  upper := p
  moves := by simpa only [path_identity] using Moves.refl p
  trace := congrArg vertices h
  finite := id
  count _ := by omega
  dimension := id
  paths r paths := paths
  span g hs := by simpa only [path_identity] using hs
  retained_value tau _ _ g := by rw [path_identity]

/-- Compose two CONSTRUCTED updates, mapping the actual earlier SOURCE moves. -/
def compose {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b)
    (q r : Path B (f a) (f b)) {n k : ℕ} (s : Update f hf p q (budget := n))
    (t : Update s.labels s.face_map s.upper (rebase (s.labels_old a) (s.labels_old b) r) (budget := k)) :
    Update f hf p r (budget := n+k) where
  Ambient := t.Ambient
  order := t.order
  complex := t.complex
  embedding := t.embedding ∘ s.embedding
  injective := t.injective.comp s.injective
  embedding_face := face_comp s.embedding s.embedding_face t.embedding t.embedding_face
  labels := t.labels
  face_map := t.face_map
  labels_old x := (t.labels_old (s.embedding x)).trans (s.labels_old x)
  upper := t.upper
  moves := by
    have hm := mapMoves t.embedding t.embedding_face s.moves
    have he := path_comp s.embedding s.embedding_face t.embedding t.embedding_face p
    exact he.symm ▸ Moves.trans hm t.moves
  trace := t.trace.trans (normalize_rebase (s.labels_old a) (s.labels_old b) r)
  finite h := t.finite (s.finite h)
  count h := by have hs := s.count h; have ht := t.count (s.finite h); omega
  dimension h := t.dimension (s.dimension h)
  paths root paths := t.paths
    ⟨s.embedding root.val,by simpa using image_mem s.embedding s.embedding_face _ root.property⟩
    (s.paths root paths)
  span g hs := by
    have ht := t.span (mapPath s.embedding s.embedding_face g) (s.span g hs)
    rw [path_comp s.embedding s.embedding_face t.embedding t.embedding_face g]
    exact ht
  retained_value tau _ _ g := by
    rw [path_comp]
    exact (t.retained_value tau (mapPath s.embedding s.embedding_face g)).trans (s.retained_value tau g)

/-- Dispatch one existing Local, computing every matching source piece internally. -/
def dispatch {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b)
    {t q : Path B (f a) (f b)} (m : Local t q) (h : Realizes f hf p t) : Update f hf p q (budget := 1) :=
  (dispatchBoth f hf m).1 p h

/-- Endpoint transport of the actual remaining schedule, preserving every operation. -/
def rebaseSchedule {B : PreAbstractSimplicialComplex W} {x y x' y' : W}
    (ex : x' = x) (ey : y' = y) {p q : Path B x y} (m : Schedule p q) :
    Schedule (rebase ex ey p) (rebase ex ey q) := by
  subst x'; subst y'; exact m

theorem size_rebaseSchedule {B : PreAbstractSimplicialComplex W} {x y x' y' : W}
    (ex : x' = x) (ey : y' = y) {p q : Path B x y} (m : Schedule p q) :
    size (rebaseSchedule ex ey m) = size m := by subst x'; subst y'; rfl

/-- Construct the joint finite source history across its changing ambient types.
The result has actual SOURCE moves and at most one new active vertex per TARGET operation. -/
def history {V : Type u} [LinearOrder V] {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {a b : V} (p : Path A a b)
    {t q : Path B (f a) (f b)} (m : Schedule t q) (h : Realizes f hf p t) :
    Update f hf p q (budget := size m) := by
  cases m with
  | nil => exact unchanged f hf p _ h
  | cons op rest =>
    let s := dispatch f hf p op h
    let next := rebaseSchedule (s.labels_old a) (s.labels_old b) rest
    let t := history (V := s.Ambient) s.labels s.face_map s.upper next (realizes f hf p _ s)
    have out := compose f hf p _ _ s t
    have hc : 1 + size next = size (Schedule.cons op rest) := by
      rw [size_rebaseSchedule]
      simp only [size,Nat.add_comm]
    exact hc ▸ out
termination_by size m
decreasing_by
  subst_vars
  simp_all only [size_rebaseSchedule,size]
  omega

/-- Transfer a prior SOURCE square stage through the constructed history. -/
def squareStage {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {r : V} (g p : Path A r r)
    (q : Path B (f r) (f r)) {n : ℕ} (s : Update f hf p q (budget := n)) (m : Moves (append g g) p) :
    Moves (append (mapPath s.embedding s.embedding_face g) (mapPath s.embedding s.embedding_face g)) s.upper := by
  have hm := mapMoves s.embedding s.embedding_face m
  rw [mapPath_append] at hm
  exact .trans hm s.moves

/-- Terminal literal trace gives the cap labels in the actual final source. -/
theorem terminalLabels {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {r : V} (p : Path A r r)
    (hr : ({f r} : Finset W) ∈ B) {n : ℕ}
    (s : Update f hf p (.refl (f r) hr) (budget := n)) :
    ∀ x ∈ vertices s.upper, s.labels x = s.labels (s.embedding r) := by
  apply realizes_constant_gives_cap_labels s.labels s.face_map s.upper
  apply vertices_injective
  exact s.trace.trans (congrArg (fun x => [x]) (s.labels_old r).symm)

/-- One actual finite exact source, constructed before any voltage iteration. -/
structure SquareSource {K : Type} [Field K] (B : PreAbstractSimplicialComplex W)
    (tau : Transport (K := K) B) (originalValue : Kˣ) (originalRoot : W) where
  Ambient : Type u
  [order : LinearOrder Ambient]
  complex : PreAbstractSimplicialComplex Ambient
  finite : Finite (Vertex complex)
  dimension : AtMostTwo complex
  root : Vertex complex
  paths : ∀ x : Vertex complex, Path complex root.val x.val
  labels : Ambient → W
  face_map : complex.map labels ≤ B
  root_label : labels root.val = originalRoot
  generator : Path complex root.val root.val
  square_moves : Moves (append generator generator) (.refl root.val root.property)
  span : CycleSpan complex (PathChains.chain (PathChains.trivialTransport complex) generator)
  exactness : (IntegerHeights.ordinaryTwo complex).range = (IntegerHeights.ordinaryOne complex).ker
  value_eq : value tau (mapPath labels face_map generator) = originalValue

attribute [instance] SquareSource.order SquareSource.finite

/-- Execute the target square schedule, cap its terminal trace and freeze the resulting source.
The input square derivation is IN THE TARGET; no source square stage is supplied. -/
def squareSource {K : Type} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W} [Finite (Vertex A)]
    (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val) (hd : AtMostTwo A)
    (g : Path A r.val r.val) (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g))
    (t : Path B (f r.val) (f r.val)) (h : Realizes f hf g t)
    (m : Moves (append t t) (.refl (f r.val) (startActive t))) :
    SquareSource.{u,w} B tau (value tau (mapPath f hf g)) (f r.val) := by
  let s := history f hf (append g g) (scheduleOfMoves m)
    (TriangleTraceUpdate.realizes_append f hf g g t t h h)
  let rg : Vertex s.complex := ⟨s.embedding r.val,by
    simpa using image_mem s.embedding s.embedding_face _ r.property⟩
  let gg := mapPath s.embedding s.embedding_face g
  let mm := squareStage f hf g (append g g) _ s (.refl _)
  have hh := terminalLabels f hf (append g g) (startActive t) s
  let C := MappedCap.cap s.complex rg.val s.upper
  let hc := MappedCap.cap_inclusion s.complex rg.val s.upper
  let fc := MappedCap.cap_map s.labels s.face_map rg.val s.upper hh
  let : Finite (Vertex s.complex) := s.finite inferInstance
  refine {
    Ambient := s.Ambient
    order := s.order
    complex := C
    finite := MappedCap.cap_finite s.complex rg.val s.upper
    dimension := MappedCap.cap_dimension s.complex rg.val s.upper (s.dimension hd)
    root := ⟨rg.val,hc rg.property⟩
    paths := MappedCap.capPaths s.complex rg.val s.upper rg (s.paths r paths)
    labels := s.labels
    face_map := fc
    root_label := s.labels_old r.val
    generator := mapPath id (identity_face_map hc) gg
    square_moves := MappedCap.cap_square_moves s.complex rg.val gg s.upper mm
    span := MappedCap.cap_cycle_span s.complex rg.val s.upper gg (s.span g hs)
    exactness := MappedCap.cap_square_exactness s.complex rg gg s.upper (s.span g hs) mm
    value_eq := ?_ }
  exact (congrArg (value tau) (MappedCap.cap_retained_path s.labels s.face_map rg.val s.upper hh gg)).trans
    (s.retained_value tau g)

/-- Every actual square-null target loop receives a finite exact mapped detecting source. -/
def sourceOfTargetSquare {K : Type} [Field K] (B : PreAbstractSimplicialComplex W)
    (tau : Transport (K := K) B) {r : W} (p : Path B r r)
    (m : Moves (append p p) (.refl r (startActive p))) :
    SquareSource.{0,w} B tau (value tau p) r := by
  let A := PolygonSource.polygon (PolygonSource.length p)
  let f := PolygonSource.labels p
  let hf := PolygonSource.labels_face p
  have mm : Moves (append p p) (.refl (f 0) (startActive p)) := m
  let s := squareSource f hf tau (PolygonSource.base (PolygonSource.length p))
    (PolygonSource.rootPaths (PolygonSource.length p)) (PolygonSource.dimension_at_most_two (PolygonSource.length p))
    (PolygonSource.forwardLoop (PolygonSource.length p)) (PolygonSource.forward_cycle_span (PolygonSource.length p))
    p (polygon_realizes_target p) mm
  exact PolygonSource.mapped_forward_loop_value tau p ▸ s

/-- Defined-chain square obstruction. Geometric pi1 and original-character adapters are separate. -/
theorem target_square_forces_noninjective {K : Type} [Field K]
    (B : PreAbstractSimplicialComplex W) (tau : Transport (K := K) B) {r : W} (p : Path B r r)
    (m : Moves (append p p) (.refl r (startActive p))) (hd : value tau p ≠ 1) :
    ¬ Function.Injective (boundaryTwo B (coeff tau)) := by
  let s := sourceOfTargetSquare B tau p m
  apply MappedCap.no_detecting_mapped_square_cap s.labels s.face_map tau s.root s.paths
    s.generator (.refl s.root.val s.root.property) s.span s.square_moves
    (by
      intro x hx
      have he : x = s.root.val := by simpa [vertices] using hx
      exact congrArg s.labels he)
  rw [s.value_eq]
  exact hd

section Guards
open InsertionTraceUpdate

def demoTarget : Path (⊤ : PreAbstractSimplicialComplex (Fin 3)) 0 2 :=
  .cons (v := 1) (Finset.insert_nonempty _ _)
    (.cons (Finset.insert_nonempty _ _) (.refl 2 (Finset.singleton_nonempty _)))

def demoShortcut : Path (⊤ : PreAbstractSimplicialComplex (Fin 3)) 0 2 :=
  single (Finset.insert_nonempty _ _)

def demoLocal : Local demoTarget demoShortcut := by
  exact Local.triangle (A := (⊤ : PreAbstractSimplicialComplex (Fin 3))) (v := 1)
    (.refl 0 (Finset.singleton_nonempty _)) (Finset.insert_nonempty _ _)
    (.refl 2 (Finset.singleton_nonempty _))

/-- Three symmetry wrappers must execute insertion, not deletion. -/
def demoNested := dispatch demoLabels demo_face_map demoPath
  (.symm (.symm (.symm demoLocal))) (by rfl)

instance demoNestedOrder : LinearOrder demoNested.Ambient := demoNested.order

theorem demo_nested_trace : vertices (imageTrace demoNested.labels demoNested.face_map demoNested.upper) = [0,1,2] :=
  demoNested.trace

theorem wrong_nested_direction_rejected :
    vertices (imageTrace demoNested.labels demoNested.face_map demoNested.upper) ≠ [0,2] := by
  rw [demo_nested_trace]
  decide

theorem wrong_retained_endpoint_label_rejected : demoNested.labels (demoNested.embedding 0) ≠ 1 := by
  rw [demoNested.labels_old]
  decide

/-- Insert then delete across a genuinely changing source ambient type. -/
def demoSchedule : Schedule demoShortcut demoShortcut :=
  .cons (.symm (.symm (.symm demoLocal))) (.cons (.symm (.symm demoLocal)) (.nil _))

def demoHistory := history demoLabels demo_face_map demoPath demoSchedule (by rfl)

instance demoHistoryOrder : LinearOrder demoHistory.Ambient := demoHistory.order

theorem demo_history_final_trace :
    vertices (imageTrace demoHistory.labels demoHistory.face_map demoHistory.upper) = [0,2] := demoHistory.trace

theorem stale_history_upper_rejected :
    vertices (imageTrace demoHistory.labels demoHistory.face_map demoHistory.upper) ≠ [0,1,2] := by
  rw [demo_history_final_trace]
  decide

theorem demo_history_count_bound : Nat.card (Vertex demoHistory.complex) ≤
    Nat.card (Vertex (⊤ : PreAbstractSimplicialComplex (Fin 2))) + 2 :=
  demoHistory.count inferInstance

/-- No actual target square witness exists for this detecting unfilled circle. -/
def circleTarget := mapPath (id : Fin 3 → Fin 3) (le_refl (cycleComplex.map id)) cycleLoop

theorem circle_detected : value LiftedImageStep.cycleImageTransport circleTarget ≠ 1 := by
  change value cycleTransport cycleLoop ≠ 1
  rw [cycleLoop_value]
  intro he
  have hh := congrArg (fun x : ℚˣ => (x : ℚ)) he
  norm_num at hh

theorem omitted_target_square_witness_rejected :
    ¬ Nonempty (Moves (append circleTarget circleTarget) (.refl 0 (startActive circleTarget))) := by
  rintro ⟨m⟩
  exact target_square_forces_noninjective _ LiftedImageStep.cycleImageTransport circleTarget m circle_detected
    VoltageTower.cycle_image_boundary_two_injective

/-- Square-nullity alone does not force weighted d2 to fail injectivity. -/
theorem omitted_detection_rejected :
    Function.Injective (boundaryTwo (PolygonSource.polygon 0)
      (coeff (PathChains.trivialTransport (K := ℚ) (PolygonSource.polygon 0)))) ∧
    Nonempty (Moves
      (append (.refl 0 (PolygonSource.singleton_face 0 0)) (.refl 0 (PolygonSource.singleton_face 0 0)))
      (.refl 0 (PolygonSource.singleton_face 0 0))) := by
  constructor
  · let := PolygonSource.triangles_empty 0
    intro x y _
    exact Subsingleton.elim x y
  · exact ⟨Moves.refl _⟩

end Guards
end D2RelationGap.LocalTraceUpdate
