import D2RelationGap.CollapsedSegments

/-!
Finite stutter normalization and literal mapped source traces.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. A normalized target trace never identifies source vertices.
General target-schedule alignment and original-character/geometric adequacy are open.
-/
noncomputable section
namespace D2RelationGap.StutterTrace
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops SourceRefinement
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

def normalize {A : PreAbstractSimplicialComplex V} {u v : V} : Path A u v → Path A u v
  | .refl u hu => .refl u hu
  | @Path.cons _ _ _ u w v h p =>
      if he : u = w then he.symm ▸ normalize p else .cons h (normalize p)

def normalizationMoves {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    Moves p (normalize p) := by
  induction p with
  | refl => exact .refl _
  | @cons u w v h p ih =>
    by_cases he : u = w
    · subst w
      simp only [normalize]
      exact .trans (.stutter (startActive p) p) ih
    · simp only [normalize,dite_eq_right he]
      exact .prepend h ih

theorem normalize_idempotent {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    normalize (normalize p) = normalize p := by
  induction p with
  | refl => rfl
  | @cons u w v h p ih =>
    by_cases he : u = w
    · subst w; simpa [normalize] using ih
    · simp only [normalize,dite_eq_right he,ih]

theorem normalize_value {K : Type*} [Field K] {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} (p : Path A u v) :
    value tau (normalize p) = value tau p := (value_moves tau (normalizationMoves p)).symm

/-- A zero normalized length detects constant VERTEX LABELS, not null-homotopy. -/
theorem normalize_length_zero_iff {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    PolygonSource.length (normalize p) = 0 ↔ ∀ x ∈ vertices p, x = u := by
  induction p with
  | refl => simp [normalize,PolygonSource.length,vertices]
  | @cons u w v h p ih =>
    by_cases he : u = w
    · subst w
      simpa [normalize,vertices] using ih
    · simp only [normalize,dite_eq_right he,PolygonSource.length,vertices]
      constructor
      · intro hn; omega
      · intro hh
        exact (he (hh w (by simp [CollapsedSegments.start_mem_vertices p])).symm).elim

def imageTrace {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) : Path B (f u) (f v) :=
  normalize (mapPath f hf p)

def Realizes {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) : Prop :=
  imageTrace f hf p = normalize q

theorem imageTrace_zero_iff_constant_labels {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) :
    PolygonSource.length (imageTrace f hf p) = 0 ↔ ∀ x ∈ vertices p, f x = f u := by
  rw [imageTrace,normalize_length_zero_iff,vertices_map]
  simp only [List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h x hx; exact h (f x) x hx rfl
  · intro h z x hx he; subst z; exact h x hx

theorem zero_length_paths_equal {A : PreAbstractSimplicialComplex V} {u v : V}
    (p q : Path A u v) (hp : PolygonSource.length p = 0) (hq : PolygonSource.length q = 0) : p = q := by
  cases p with
  | refl u hu =>
    cases q with
    | refl => rfl
    | cons h q => simp [PolygonSource.length] at hq
  | cons h p => simp [PolygonSource.length] at hp

theorem normalize_append_left {A : PreAbstractSimplicialComplex V} {u v w : V}
    (p : Path A u v) (q : Path A v w) :
    normalize (append p q) = normalize (append (normalize p) q) := by
  induction p with
  | refl => rfl
  | @cons u t v h p ih =>
    by_cases he : u = t
    · subst t; simpa [append,normalize] using ih q
    · simpa [append,normalize,he] using congrArg (Path.cons h) (ih q)

theorem normalize_prefix_congr {A : PreAbstractSimplicialComplex V} {x u v : V}
    (pre : Path A x u) (p q : Path A u v) (h : normalize p = normalize q) :
    normalize (append pre p) = normalize (append pre q) := by
  induction pre with
  | refl => exact h
  | @cons x t u hx pre ih =>
    by_cases he : x = t
    · subst t; simpa [append,normalize] using ih p q h
    · simpa [append,normalize,he] using congrArg (Path.cons hx) (ih p q h)

theorem normalize_context_congr {A : PreAbstractSimplicialComplex V} {x u v y : V}
    (pre : Path A x u) (p q : Path A u v) (post : Path A v y) (h : normalize p = normalize q) :
    normalize (append pre (append p post)) = normalize (append pre (append q post)) := by
  apply normalize_prefix_congr
  rw [normalize_append_left p post,normalize_append_left q post,h]

theorem normalize_append_right {A : PreAbstractSimplicialComplex V} {u v w : V}
    (p : Path A u v) (q : Path A v w) :
    normalize (append p q) = normalize (append p (normalize q)) :=
  normalize_prefix_congr p q (normalize q) (normalize_idempotent q).symm

theorem polygon_realizes_target {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    Realizes (PolygonSource.labels p) (PolygonSource.labels_face p)
      (PolygonSource.forwardLoop (PolygonSource.length p)) p := by
  have hh : normalize (padded p) = normalize p := by
    simp only [padded,normalize,eq_self,dite_true]
    rw [normalize_append_right]
    simp [single,normalize,append_right_refl]
  exact (congrArg (fun q : Path A r r => normalize q) (mapped_forward_eq_padded p)).trans hh

theorem segment_shortening_preserves_imageTrace {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (hl : ∀ x ∈ vertices p, f x = f v) :
    imageTrace f (MappedCap.cap_map f hf v p hl)
      (mapPath id (TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A v p)) p) =
    imageTrace f (MappedCap.cap_map f hf v p hl) (CollapsedSegments.shortcut A p) := by
  have hu := hl u (CollapsedSegments.start_mem_vertices p)
  apply zero_length_paths_equal
  · change PolygonSource.length (normalize (mapPath f _ (mapPath id _ p))) = 0
    rw [MappedCap.cap_retained_path f hf v p hl p]
    exact (imageTrace_zero_iff_constant_labels f hf p).mpr (fun x hx => (hl x hx).trans hu.symm)
  · apply (imageTrace_zero_iff_constant_labels f _ _).mpr
    intro x hx
    rw [CollapsedSegments.shortcut_vertices] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · rfl
    · exact hu.symm

theorem contextual_segment_shortening_preserves_trace {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {x u v y : V}
    (pre : Path A x u) (p : Path A u v) (post : Path A v y)
    (hl : ∀ z ∈ vertices p, f z = f v) :
    imageTrace f (MappedCap.cap_map f hf v p hl)
      (mapPath id (TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A v p))
        (append pre (append p post))) =
    imageTrace f (MappedCap.cap_map f hf v p hl)
      (append (mapPath id (TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A v p)) pre)
        (append (CollapsedSegments.shortcut A p)
          (mapPath id (TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A v p)) post))) := by
  simp only [imageTrace,mapPath_append]
  apply normalize_context_congr
  exact segment_shortening_preserves_imageTrace f hf p hl

/-- The terminal trace invariant supplies EXACTLY the constant-label cap condition. -/
theorem realizes_constant_gives_cap_labels {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {r : V} (p : Path A r r)
    (h : Realizes f hf p (.refl (f r) (by simpa using image_mem f hf _ (startActive p)))) :
    ∀ x ∈ vertices p, f x = f r := by
  apply (imageTrace_zero_iff_constant_labels f hf p).mp
  change imageTrace f hf p = .refl (f r) _ at h
  rw [h]
  rfl

theorem terminal_trace_supplies_square_cap {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (g p : Path A r.val r.val)
    (hs : TriangleAttachment.CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g))
    (m : Moves (append g g) p)
    (ht : Realizes f hf p (.refl (f r.val) (by simpa using image_mem f hf _ r.property)))
    (hd : value tau (mapPath f hf g) ≠ 1) :
    ¬ Function.Injective (boundaryTwo B (coeff tau)) :=
  MappedCap.no_detecting_mapped_square_cap f hf tau r paths g p hs m
    (realizes_constant_gives_cap_labels f hf p ht) hd

theorem collapsed_trace_does_not_make_source_constant :
    PolygonSource.length (imageTrace (fun _ : Fin 3 => (0 : Fin 1))
      (B := (⊤ : PreAbstractSimplicialComplex (Fin 1)))
      (by rintro s ⟨t,ht,rfl⟩; exact ht.1.image _) CollapsedSegments.distinctSegment) = 0 ∧
    vertices CollapsedSegments.distinctSegment = [0,1] ∧ (0 : Fin 3) ≠ 1 := by
  constructor
  · apply (imageTrace_zero_iff_constant_labels _ _ _).mpr; intro x hx; rfl
  constructor
  · rfl
  · decide

theorem backtrack_is_not_erased_by_stutter_normalization :
    ∃ p : Path cycleComplex 0 0, Nonempty (Moves p (.refl 0 cycleBase.property)) ∧
      PolygonSource.length (normalize p) = 2 := by
  let p : Path cycleComplex 0 0 := .cons (v := 1) (by constructor <;> simp)
    (.cons (v := 0) (by constructor <;> simp) (.refl 0 cycleBase.property))
  refine ⟨p,⟨.backtrack _ _⟩,?_⟩
  simp [p,normalize,PolygonSource.length]

end D2RelationGap.StutterTrace
