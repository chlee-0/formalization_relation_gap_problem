import D2RelationGap.MappedCap

/-!
Actual mapped constant-label source segments shortened without merging vertices.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Aligning an arbitrary target schedule with these source
segments and constructing the joint source strip remain open.
-/
noncomputable section
namespace D2RelationGap.CollapsedSegments
open OrientedSimplices SimplicialTransport IntegerHeights EdgePaths BasedLoops
open TriangleAttachment SourceRefinement SourceMoveSimulation MappedCap
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

theorem start_mem_vertices {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    u ∈ vertices p := by cases p <;> simp [vertices]

def shortcut (A : PreAbstractSimplicialComplex V) {u v : V} (p : Path A u v) : Path (cap A v p) u v :=
  single (by simpa only [Finset.pair_comm] using cone_edge A v p)

/-- An actual finite SOURCE derivation keeps BOTH segment endpoints. -/
def shortcut_moves (A : PreAbstractSimplicialComplex V) {u v : V} (p : Path A u v) :
    Moves (mapPath id (identity_face_map (cap_inclusion A v p)) p) (shortcut A p) := by
  induction p with
  | refl u hu => exact .symm (.stutter hu (.refl u hu))
  | @cons u w v h q ih =>
    have hm := mapMoves id (identity_face_map (inclusion (cap A v q) v w u)) ih
    rw [included_path_comp (cap_inclusion A v q) (inclusion (cap A v q) v w u) q] at hm
    refine .trans (.prepend _ hm) ?_
    have ht : ({u,w,v} : Finset V) ∈ attachment (cap A v q) v w u := by
      have he : ({u,w,v} : Finset V) = {v,w,u} := by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      rw [he]; exact triangle_face _ _ _ _
    exact .triangle ht (.refl v (cap_inclusion A v (.cons h q) (endActive (.cons h q))))

def contextual_shortcut_moves (A : PreAbstractSimplicialComplex V) {x u v y : V}
    (pre : Path A x u) (p : Path A u v) (post : Path A v y) :
    Moves (mapPath id (identity_face_map (cap_inclusion A v p)) (append pre (append p post)))
      (append (mapPath id (identity_face_map (cap_inclusion A v p)) pre)
        (append (shortcut A p) (mapPath id (identity_face_map (cap_inclusion A v p)) post))) := by
  rw [mapPath_append,mapPath_append]
  exact prefixMoves _ (.suffix _ (shortcut_moves A p))

theorem shortcut_vertices (A : PreAbstractSimplicialComplex V) {u v : V} (p : Path A u v) :
    vertices (shortcut A p) = [u,v] := rfl

theorem shortcut_target_vertices {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (hl : ∀ x ∈ vertices p, f x = f v) :
    vertices (mapPath f (cap_map f hf v p hl) (shortcut A p)) = [f v,f v] := by
  rw [vertices_map,shortcut_vertices]
  simp only [List.map_cons,List.map_nil,hl u (start_mem_vertices p)]

theorem shortcut_target_value {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B) {u v : V}
    (p : Path A u v) (hl : ∀ x ∈ vertices p, f x = f v) :
    value tau (mapPath f (cap_map f hf v p hl) (shortcut A p)) = 1 := by
  change tau.unit (f u) (f v) * 1 = 1
  rw [hl u (start_mem_vertices p)]
  have hv : ({f v} : Finset W) ∈ B := by simpa using image_mem f hf _ (endActive p)
  simp [diagonal_unit tau (f v) hv]

/-- The old distinguished loop remains available while a collapsed segment is shortened. -/
theorem segment_retains_source_state {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B)
    {u v : V} (p : Path A u v) (hl : ∀ x ∈ vertices p, f x = f v)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (hd : SimplicialImages.AtMostTwo A) (g : Path A r.val r.val)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    Finite (Vertex (cap A v p)) ∧ SimplicialImages.AtMostTwo (cap A v p) ∧
    Nat.card (Vertex (cap A v p)) = Nat.card (Vertex A) ∧
    Nonempty (∀ x : Vertex (cap A v p), Path (cap A v p) r.val x.val) ∧
    CycleSpan (cap A v p) (PathChains.chain (PathChains.trivialTransport (cap A v p))
      (mapPath id (identity_face_map (cap_inclusion A v p)) g)) ∧
    value tau (mapPath f (cap_map f hf v p hl)
      (mapPath id (identity_face_map (cap_inclusion A v p)) g)) = value tau (mapPath f hf g) :=
  ⟨cap_finite A v p,cap_dimension A v p hd,cap_count A v p,
    ⟨capPaths A v p r paths⟩,cap_cycle_span A v p g hs,
    congrArg (value tau) (cap_retained_path f hf v p hl g)⟩

def distinctSegment : Path cycleComplex 0 1 := single (by constructor <;> simp)

theorem target_stutter_does_not_identify_source_endpoints :
    vertices (shortcut cycleComplex distinctSegment) = [0,1] ∧
    (vertices (shortcut cycleComplex distinctSegment)).map (fun _ : Fin 3 => (0 : Fin 1)) = [0,0] ∧
    (0 : Fin 3) ≠ 1 := by
  constructor
  · rfl
  constructor <;> decide

theorem missing_constant_segment_labels_rejected :
    ¬ (∀ x ∈ vertices cycleLoop, (id : Fin 3 → Fin 3) x = id 0) ∧
    ¬ (cap cycleComplex 0 cycleLoop).map (id : Fin 3 → Fin 3) ≤ cycleComplex := by
  constructor
  · intro h
    have hh := h 1 (by simp [vertices,cycleLoop])
    norm_num at hh
  · exact omitted_constant_labels_rejected

end D2RelationGap.CollapsedSegments
