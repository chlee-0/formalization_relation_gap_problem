import D2RelationGap.SourceMoveSimulation

/-!
A finite mapped cap for a source path whose target labels are constant.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Producing the constant-label upper path from an arbitrary
target move derivation, and original-character/geometric adequacy, remain open.
-/
noncomputable section
namespace D2RelationGap.MappedCap
open OrientedSimplices SimplicialTransport IntegerHeights EdgePaths BasedLoops
open TriangleAttachment SourceRefinement SourceMoveSimulation
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- Successive triangle attachments, in reverse path order; no new vertices. -/
def cap (A : PreAbstractSimplicialComplex V) (r : V) {u : V} :
    Path A u r → PreAbstractSimplicialComplex V
  | .refl _ _ => A
  | @Path.cons _ _ _ u v _ _ q => attachment (cap A r q) r v u

theorem cap_inclusion (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r) :
    A ≤ cap A r p := by
  induction p with
  | refl => exact le_refl _
  | cons h q ih => exact ih.trans (inclusion _ _ _ _)

theorem cone_edge (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r) :
    ({r,u} : Finset V) ∈ cap A r p := by
  cases p with
  | refl u hu => simpa [cap] using hu
  | @cons u v _ h q =>
    exact pair_mem_of_face _ _ (triangle_face (cap A r q) r v u) r u (by simp) (by simp)

theorem cap_vertex_old (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r)
    (x : Vertex (cap A r p)) : ({x.val} : Finset V) ∈ A := by
  induction p with
  | refl => exact x.property
  | @cons u v r h q ih =>
    have hrev : ({v,u} : Finset V) ∈ A := by simpa only [Finset.pair_comm] using h
    have hvu : ({v,u} : Finset V) ∈ cap A r q := cap_inclusion A r q hrev
    exact ih ⟨x.val,vertex_old _ r v u (cone_edge A r q) hvu x⟩

def capVertices (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r) :
    Vertex (cap A r p) ≃ Vertex A where
  toFun x := ⟨x.val,cap_vertex_old A r p x⟩
  invFun := vertexInclusion (cap_inclusion A r p)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem cap_finite (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r)
    [Finite (Vertex A)] : Finite (Vertex (cap A r p)) :=
  Finite.of_equiv _ (capVertices A r p).symm

theorem cap_count (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r) :
    Nat.card (Vertex (cap A r p)) = Nat.card (Vertex A) := Nat.card_congr (capVertices A r p)

theorem cap_dimension (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r)
    (hd : SimplicialImages.AtMostTwo A) : SimplicialImages.AtMostTwo (cap A r p) := by
  induction p with
  | refl => exact hd
  | cons h q ih => exact dimension_at_most_two _ _ _ _ ih

def capPaths (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r)
    (s : Vertex A) (paths : ∀ x : Vertex A, Path A s.val x.val) :
    ∀ x : Vertex (cap A r p), Path (cap A r p) s.val x.val :=
  fun x => mapPath id (identity_face_map (cap_inclusion A r p)) (paths ((capVertices A r p) x))

theorem included_path_comp {A B C : PreAbstractSimplicialComplex V} (hAB : A ≤ B) (hBC : B ≤ C)
    {x y : V} (p : Path A x y) :
    mapPath id (identity_face_map hBC) (mapPath id (identity_face_map hAB) p) =
      mapPath id (identity_face_map (hAB.trans hBC)) p := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih

theorem included_path_identity {A : PreAbstractSimplicialComplex V} (hAA : A ≤ A)
    {x y : V} (p : Path A x y) : mapPath id (identity_face_map hAA) p = p := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih

theorem cap_cycle_span (A : PreAbstractSimplicialComplex V) (r : V) {u s : V}
    (p : Path A u r) (g : Path A s s)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    CycleSpan (cap A r p) (PathChains.chain (PathChains.trivialTransport (cap A r p))
      (mapPath id (identity_face_map (cap_inclusion A r p)) g)) := by
  induction p with
  | refl =>
    change CycleSpan A (PathChains.chain (PathChains.trivialTransport A)
      (mapPath id (identity_face_map (le_refl A)) g))
    rw [included_path_identity (le_refl A) g]
    exact hs
  | @cons u v r h q ih =>
    have hrev : ({v,u} : Finset V) ∈ A := by simpa only [Finset.pair_comm] using h
    have hvu : ({v,u} : Finset V) ∈ cap A r q := cap_inclusion A r q hrev
    have hh := attached_loop_cycle_span (cap A r q) r v u (cone_edge A r q) hvu
      (mapPath id (identity_face_map (cap_inclusion A r q)) g) ih
    rw [included_path_comp (cap_inclusion A r q) (inclusion (cap A r q) r v u) g] at hh
    exact hh

/-- The cone-prefix path contracts by literal finite source triangle moves. -/
def cap_null_moves (A : PreAbstractSimplicialComplex V) (r : V) {u : V} (p : Path A u r) :
    Moves (.cons (cone_edge A r p) (mapPath id (identity_face_map (cap_inclusion A r p)) p))
      (.refl r (cap_inclusion A r p (endActive p))) := by
  induction p with
  | refl u hu => exact .stutter hu (.refl u hu)
  | @cons u v r h q ih =>
    have ht : ({r,u,v} : Finset V) ∈ attachment (cap A r q) r v u := by
      have he : ({r,u,v} : Finset V) = {r,v,u} := by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      rw [he]; exact triangle_face _ _ _ _
    refine .trans (.triangle ht _) ?_
    have hm := mapMoves id (identity_face_map (inclusion (cap A r q) r v u)) ih
    simp only [mapPath,id_eq] at hm
    rw [included_path_comp (cap_inclusion A r q) (inclusion (cap A r q) r v u) q] at hm
    exact hm

def cap_loop_moves (A : PreAbstractSimplicialComplex V) (r : V) (p : Path A r r) :
    Moves (mapPath id (identity_face_map (cap_inclusion A r p)) p)
      (.refl r (cap_inclusion A r p (endActive p))) := by
  have hm := cap_null_moves A r p
  exact .trans (.symm (.stutter (cap_inclusion A r p (startActive p)) _)) hm

theorem cap_loop_null (A : PreAbstractSimplicialComplex V) (r : V) (p : Path A r r) :
    Nonempty (Moves (mapPath id (identity_face_map (cap_inclusion A r p)) p)
      (.refl r (cap_inclusion A r p (endActive p)))) := ⟨cap_loop_moves A r p⟩

/-- Every new cap triangle collapses to an actual singleton target face. -/
theorem cap_map {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (r : V) {u : V} (p : Path A u r)
    (hl : ∀ x ∈ vertices p, f x = f r) : (cap A r p).map f ≤ B := by
  induction p with
  | refl => exact hf
  | @cons u v r h q ih =>
    have hq : ∀ x ∈ vertices q, f x = f r := fun x hx => hl x (by simp [vertices,hx])
    have hu : f u = f r := hl u (by simp [vertices])
    have hv : f v = f r := hq v (by cases q <;> simp [vertices])
    apply mapped_face (cap A r q) B r v u f (ih hq)
    have hr : ({f r} : Finset W) ∈ B := by simpa using image_mem f hf _ (endActive (.cons h q))
    simpa [hu,hv] using hr

theorem cap_retained_path {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (r : V) {u : V} (p : Path A u r)
    (hl : ∀ x ∈ vertices p, f x = f r) {x y : V} (g : Path A x y) :
    mapPath f (cap_map f hf r p hl) (mapPath id (identity_face_map (cap_inclusion A r p)) g) =
      mapPath f hf g := by
  induction g with
  | refl => rfl
  | cons h g ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih

/-- An actual upper SOURCE loop represents the square before it is capped. -/
def cap_square_moves (A : PreAbstractSimplicialComplex V) (r : V) (g p : Path A r r)
    (m : Moves (append g g) p) :
    Moves (append (mapPath id (identity_face_map (cap_inclusion A r p)) g)
      (mapPath id (identity_face_map (cap_inclusion A r p)) g))
      (.refl r (cap_inclusion A r p (endActive p))) := by
  have hm := mapMoves id (identity_face_map (cap_inclusion A r p)) m
  rw [mapPath_append] at hm
  exact .trans hm (cap_loop_moves A r p)

theorem cap_square_exactness (A : PreAbstractSimplicialComplex V) (r : Vertex A)
    (g p : Path A r.val r.val)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g))
    (m : Moves (append g g) p) :
    (ordinaryTwo (cap A r.val p)).range = (ordinaryOne (cap A r.val p)).ker :=
  exactness_of_square_moves (cap A r.val p)
    ⟨r.val,cap_inclusion A r.val p r.property⟩
    (mapPath id (identity_face_map (cap_inclusion A r.val p)) g)
    (cap_cycle_span A r.val p g hs) (cap_square_moves A r.val g p m)

theorem cap_exactness_of_spanning_loop (A : PreAbstractSimplicialComplex V) (r : V)
    (p : Path A r r) (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) p)) :
    (ordinaryTwo (cap A r p)).range = (ordinaryOne (cap A r p)).ker := by
  have hh := cycle_span_moves (cap A r p)
    (mapPath id (identity_face_map (cap_inclusion A r p)) p)
    (.refl r (cap_inclusion A r p (endActive p))) (cap_cycle_span A r p p hs) (cap_loop_moves A r p)
  simp only [PathChains.chain] at hh
  exact (zero_span_iff_exactness _).mp hh

/-- This is a completed local cap package. The supplied square-to-upper derivation
is IN THE SOURCE; obtaining it from arbitrary target moves is still open. -/
theorem mapped_square_cap {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (hd : SimplicialImages.AtMostTwo A) (g p : Path A r.val r.val)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g))
    (m : Moves (append g g) p) (hl : ∀ x ∈ vertices p, f x = f r.val) :
    ∃ (C : PreAbstractSimplicialComplex V) (hAC : A ≤ C) (hC : C.map f ≤ B),
      Finite (Vertex C) ∧ SimplicialImages.AtMostTwo C ∧ Nat.card (Vertex C) = Nat.card (Vertex A) ∧
      Nonempty (∀ x : Vertex C, Path C r.val x.val) ∧
      (ordinaryTwo C).range = (ordinaryOne C).ker ∧
      Nonempty (Moves (append (mapPath id (identity_face_map hAC) g)
        (mapPath id (identity_face_map hAC) g)) (.refl r.val (hAC r.property))) ∧
      value tau (mapPath f hC (mapPath id (identity_face_map hAC) g)) = value tau (mapPath f hf g) := by
  refine ⟨cap A r.val p,cap_inclusion A r.val p,cap_map f hf r.val p hl,
    cap_finite A r.val p,cap_dimension A r.val p hd,cap_count A r.val p,
    ⟨capPaths A r.val p r paths⟩,cap_square_exactness A r g p hs m,
    ⟨cap_square_moves A r.val g p m⟩,?_⟩
  exact congrArg (value tau) (cap_retained_path f hf r.val p hl g)

/-- The completed cap is frozen as the ONE source used by the checked image
induction. The square-to-upper SOURCE derivation and constant labels stay explicit. -/
theorem no_detecting_mapped_square_cap {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (g p : Path A r.val r.val)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g))
    (m : Moves (append g g) p) (hl : ∀ x ∈ vertices p, f x = f r.val)
    (hd : value tau (mapPath f hf g) ≠ 1) :
    ¬ Function.Injective (boundaryTwo B (coeff tau)) := by
  intro h2
  let C := cap A r.val p
  let hC : C.map f ≤ B := cap_map f hf r.val p hl
  let tau' := pullback tau id (identity_face_map hC)
  let g' := mapPath id (identity_face_map (cap_inclusion A r.val p)) g
  let : Finite (Vertex C) := cap_finite A r.val p
  have h2' : Function.Injective (boundaryTwo (C.map f) (coeff tau')) := by
    change Function.Injective (boundaryTwo (C.map f) (coeff tau))
    exact subcomplex_two_injective hC (coeff tau) h2
  have hv := VoltageTower.source_holonomy_trivial C
    ⟨r.val,cap_inclusion A r.val p r.property⟩ (capPaths A r.val p r paths)
    (cap_square_exactness A r g p hs m) W f tau' h2' (Quotient.mk _ g')
  change value (pullback tau f hC) g' = 1 at hv
  have hh : value tau (mapPath f hC g') = 1 := (value_mapPath tau f hC g').trans hv
  have he := cap_retained_path f hf r.val p hl g
  exact hd ((congrArg (value tau) he).symm.trans hh)

theorem omitted_constant_labels_rejected :
    ¬ (cap cycleComplex 0 cycleLoop).map (id : Fin 3 → Fin 3) ≤ cycleComplex := by
  intro hf
  have ht : ({0,2,1} : Finset (Fin 3)) ∈ cap cycleComplex 0 cycleLoop :=
    Or.inl (triangle_face _ 0 2 1)
  have hh := image_mem id hf _ ht
  have hc : ({0,2,1} : Finset (Fin 3)).card ≤ 2 := by simpa using hh.2
  norm_num at hc

theorem cap_exactness_reflection_rejected (n : ℕ) :
    (ordinaryTwo (cap (PolygonSource.polygon n) 0 (PolygonSource.forwardLoop n))).range =
      (ordinaryOne (cap (PolygonSource.polygon n) 0 (PolygonSource.forwardLoop n))).ker ∧
    (ordinaryTwo (PolygonSource.polygon n)).range ≠ (ordinaryOne (PolygonSource.polygon n)).ker :=
  ⟨cap_exactness_of_spanning_loop _ 0 _ (PolygonSource.forward_cycle_span n),
    PolygonSource.unfilled_polygon_exactness_rejected n⟩

theorem uncapped_contraction_rejected :
    Nonempty (Moves (mapPath id (identity_face_map (cap_inclusion cycleComplex 0 cycleLoop)) cycleLoop)
      (.refl 0 (cap_inclusion cycleComplex 0 cycleLoop cycleBase.property))) ∧
    ¬ Nonempty (Moves cycleLoop (.refl 0 cycleBase.property)) :=
  ⟨cap_loop_null _ 0 cycleLoop,nonexistent_triangle_shortcut_rejected⟩

/-- A constant empty upper path alone does not make the original source exact. -/
theorem omitted_square_to_upper_moves_rejected (n : ℕ) :
    (ordinaryTwo (cap (PolygonSource.polygon n) 0
      (.refl 0 (PolygonSource.singleton_face n 0)))).range ≠
    (ordinaryOne (cap (PolygonSource.polygon n) 0
      (.refl 0 (PolygonSource.singleton_face n 0)))).ker :=
  PolygonSource.unfilled_polygon_exactness_rejected n

end D2RelationGap.MappedCap
