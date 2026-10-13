import D2RelationGap.TraceAlignment

/-!
Actual source updates of literal target triangle traces.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
General schedule iteration and original-character/geometric adequacy remain open.
-/
noncomputable section
namespace D2RelationGap.TriangleTraceUpdate
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops IntegerHeights
open SourceRefinement SourceMoveSimulation TriangleAttachment StutterTrace TraceAlignment MappedCap
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- The middle source block is capped without identifying its endpoints. -/
def blockComplex (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c) :=
  attachment (attachment (MappedCap.cap A c mid) a b c) a c d

theorem block_inclusion (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c) :
    A ≤ blockComplex A a b c d mid :=
  (MappedCap.cap_inclusion A c mid).trans ((inclusion _ a b c).trans (inclusion _ a c d))

theorem block_face_map {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (a b c d : V) (mid : Path A b c)
    (hl : ∀ z ∈ vertices mid, f z = f c) (ht : ({f a,f c,f d} : Finset W) ∈ B) :
    (blockComplex A a b c d mid).map f ≤ B := by
  have hb := hl b (CollapsedSegments.start_mem_vertices mid)
  have hcap := MappedCap.cap_map f hf c mid hl
  have habc : ({f a,f b,f c} : Finset W) ∈ B := by
    rw [hb]
    have hh := pair_mem_of_face _ _ ht (f a) (f c) (by simp) (by simp)
    simpa using hh
  exact mapped_face _ B a c d f (mapped_face _ B a b c f hcap habc) ht

def blockUpper (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c)
    {u v : V} (pre : Path A u a) (post : Path A d v) : Path (blockComplex A a b c d mid) u v :=
  append (mapPath id (identity_face_map (block_inclusion A a b c d mid)) pre)
    (.cons (pair_mem_of_face _ _ (triangle_face _ a c d) a d (by simp) (by simp))
      (mapPath id (identity_face_map (block_inclusion A a b c d mid)) post))

/-- Explicit SOURCE moves: cap the middle block, then delete two actual triangles. -/
def block_moves (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c)
    (hab : ({a,b} : Finset V) ∈ A) (hcd : ({c,d} : Finset V) ∈ A)
    {u v : V} (pre : Path A u a) (post : Path A d v) :
    Moves (mapPath id (identity_face_map (block_inclusion A a b c d mid))
      (append pre (.cons hab (append mid (.cons hcd post))))) (blockUpper A a b c d mid pre post) := by
  let C := MappedCap.cap A c mid
  let D := attachment C a b c
  let E := attachment D a c d
  let iC := identity_face_map (MappedCap.cap_inclusion A c mid)
  let iD := identity_face_map (inclusion C a b c)
  let iE := identity_face_map (inclusion D a c d)
  have mC := CollapsedSegments.contextual_shortcut_moves A (append pre (single hab)) mid (.cons hcd post)
  have mD := mapMoves id iD mC
  have mE := mapMoves id iE mD
  have m1 := attached_shortcut_moves C a b c (MappedCap.cap_inclusion A c mid hab)
    (by simpa only [Finset.pair_comm] using MappedCap.cone_edge A c mid)
    (mapPath id iC pre) (mapPath id iC (.cons hcd post))
  have m1E := mapMoves id iE m1
  have m2 := attached_shortcut_moves D a c d
    (pair_mem_of_face _ _ (triangle_face C a b c) a c (by simp) (by simp))
    ((inclusion C a b c) (MappedCap.cap_inclusion A c mid hcd))
    (mapPath id iD (mapPath id iC pre)) (mapPath id iD (mapPath id iC post))
  simp only [attachedShortcut,CollapsedSegments.shortcut,single,mapPath_append,append_assoc,
    mapPath,append] at mE m1E m2
  have m := Moves.trans mE (Moves.trans m1E m2)
  have hcomp {x y : V} (p : Path A x y) :
      mapPath id iE (mapPath id iD (mapPath id iC p)) =
        mapPath id (identity_face_map (block_inclusion A a b c d mid)) p :=
    (congrArg (mapPath id iE) (included_path_comp (MappedCap.cap_inclusion A c mid)
      (inclusion C a b c) p)).trans
      (included_path_comp ((MappedCap.cap_inclusion A c mid).trans (inclusion C a b c))
        (inclusion D a c d) p)
  rw [hcomp pre,hcomp mid,hcomp post] at m
  let hi := identity_face_map (block_inclusion A a b c d mid)
  have heq : mapPath id hi (append pre (.cons hab (append mid (.cons hcd post)))) =
      append (mapPath id hi pre) (.cons (block_inclusion A a b c d mid hab)
        (append (mapPath id hi mid) (.cons (block_inclusion A a b c d mid hcd) (mapPath id hi post)))) := by
    rw [mapPath_append]
    change append _ (.cons _ (mapPath id hi (append mid (.cons hcd post)))) = _
    rw [mapPath_append]
    rfl
  exact heq.symm ▸ m

theorem block_retained_path {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (a b c d : V) (mid : Path A b c)
    (hl : ∀ z ∈ vertices mid, f z = f c) (ht : ({f a,f c,f d} : Finset W) ∈ B)
    {u v : V} (p : Path A u v) :
    mapPath f (block_face_map f hf a b c d mid hl ht)
      (mapPath id (identity_face_map (block_inclusion A a b c d mid)) p) = mapPath f hf p := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih


theorem blockUpper_trace {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (a b c d : V) (mid : Path A b c)
    (hl : ∀ z ∈ vertices mid, f z = f c) (ht : ({f a,f c,f d} : Finset W) ∈ B)
    {u v : V} (pre : Path A u a) (post : Path A d v)
    (hp : ∀ z ∈ vertices pre, f z = f a) :
    vertices (imageTrace f (block_face_map f hf a b c d mid hl ht)
      (blockUpper A a b c d mid pre post)) =
      if f a = f d then vertices (imageTrace f hf post) else f a :: vertices (imageTrace f hf post) := by
  let hi := identity_face_map (block_inclusion A a b c d mid)
  let hmap := block_face_map f hf a b c d mid hl ht
  have hpre : ∀ z ∈ vertices (mapPath id hi pre), f z = f a := by
    simpa only [vertices_map,List.map_id] using hp
  rw [blockUpper,constant_before_trace f hmap _ _ hpre]
  have hpost : imageTrace f hmap (mapPath id hi post) = imageTrace f hf post :=
    congrArg StutterTrace.normalize (block_retained_path f hf a b c d mid hl ht post)
  have hface : ({a,d} : Finset V) ∈ blockComplex A a b c d mid :=
    pair_mem_of_face _ _ (triangle_face _ a c d) a d (by simp) (by simp)
  exact (imageTrace_cons_vertices f hmap hface (mapPath id hi post)).trans (by rw [hpost])

theorem block_vertex_old (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c)
    (hab : ({a,b} : Finset V) ∈ A) (hcd : ({c,d} : Finset V) ∈ A)
    (x : Vertex (blockComplex A a b c d mid)) : ({x.val} : Finset V) ∈ A := by
  have hbc : ({b,c} : Finset V) ∈ cap A c mid := by simpa only [Finset.pair_comm] using cone_edge A c mid
  have hac : ({a,c} : Finset V) ∈ attachment (cap A c mid) a b c :=
    pair_mem_of_face _ _ (triangle_face _ a b c) a c (by simp) (by simp)
  have hxD := TriangleAttachment.vertex_old (attachment (cap A c mid) a b c) a c d hac
    ((inclusion _ a b c) (cap_inclusion A c mid hcd)) x
  have hxC := TriangleAttachment.vertex_old (cap A c mid) a b c (cap_inclusion A c mid hab) hbc ⟨x.val,hxD⟩
  exact cap_vertex_old A c mid ⟨x.val,hxC⟩

theorem block_dimension (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c)
    (hd : SimplicialImages.AtMostTwo A) : SimplicialImages.AtMostTwo (blockComplex A a b c d mid) :=
  dimension_at_most_two _ a c d (dimension_at_most_two _ a b c (cap_dimension A c mid hd))

theorem block_span (A : PreAbstractSimplicialComplex V) (a b c d : V) (mid : Path A b c)
    (hab : ({a,b} : Finset V) ∈ A) (hcd : ({c,d} : Finset V) ∈ A)
    {r : V} (g : Path A r r) (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    CycleSpan (blockComplex A a b c d mid) (PathChains.chain (PathChains.trivialTransport _)
      (mapPath id (identity_face_map (block_inclusion A a b c d mid)) g)) := by
  have hbc : ({b,c} : Finset V) ∈ cap A c mid := by simpa only [Finset.pair_comm] using cone_edge A c mid
  have hac : ({a,c} : Finset V) ∈ attachment (cap A c mid) a b c :=
    pair_mem_of_face _ _ (triangle_face _ a b c) a c (by simp) (by simp)
  have h1 := attached_loop_cycle_span (cap A c mid) a b c (cap_inclusion A c mid hab) hbc
    (mapPath id (identity_face_map (cap_inclusion A c mid)) g) (cap_cycle_span A c mid g hs)
  have h2 := attached_loop_cycle_span (attachment (cap A c mid) a b c) a c d hac
    ((inclusion _ a b c) (cap_inclusion A c mid hcd))
    (mapPath id (identity_face_map (inclusion _ a b c)) (mapPath id (identity_face_map (cap_inclusion A c mid)) g)) h1
  have hg : mapPath id (identity_face_map (inclusion _ a c d))
      (mapPath id (identity_face_map (inclusion _ a b c)) (mapPath id (identity_face_map (cap_inclusion A c mid)) g)) =
      mapPath id (identity_face_map (block_inclusion A a b c d mid)) g :=
    (congrArg (mapPath id (identity_face_map (inclusion _ a c d)))
      (included_path_comp (cap_inclusion A c mid) (inclusion _ a b c) g)).trans
      (included_path_comp ((cap_inclusion A c mid).trans (inclusion _ a b c)) (inclusion _ a c d) g)
  exact (congrArg (fun p => CycleSpan (blockComplex A a b c d mid)
    (PathChains.chain (PathChains.trivialTransport _) p)) hg).mp h2

/-- A locally constructed source extension; no lifting or exactness field is assumed. -/
structure Deletion {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (target : Path B (f u) (f v)) where
  complex : PreAbstractSimplicialComplex V
  inclusion : A ≤ complex
  face_map : complex.map f ≤ B
  upper : Path complex u v
  moves : Moves (mapPath id (identity_face_map inclusion) p) upper
  realizes : Realizes f face_map upper target
  vertex_old : ∀ x : Vertex complex, ({x.val} : Finset V) ∈ A
  dimension : SimplicialImages.AtMostTwo A → SimplicialImages.AtMostTwo complex
  span : ∀ {r : V} (g : Path A r r), CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g) →
    CycleSpan complex (PathChains.chain (PathChains.trivialTransport _) (mapPath id (identity_face_map inclusion) g))

/-- Extract both edges and the collapsed middle block before constructing the update. -/
def deleteTwo {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (b c : W) (q : Path B c (f v))
    (he : vertices (imageTrace f hf p) = f u :: b :: vertices (StutterTrace.normalize q))
    (ht : ({f u,b,c} : Finset W) ∈ B) :
    Deletion f p (.cons (pair_mem_of_face _ _ ht (f u) c (by simp) (by simp)) q) := by
  have he' : vertices (imageTrace f hf p) = f u :: b :: c :: (vertices (StutterTrace.normalize q)).tail := by
    exact he.trans (congrArg (fun xs => f u :: b :: xs) (vertices_eq_start_tail (StutterTrace.normalize q)))
  let t := twoSplit f hf p b c (vertices (StutterTrace.normalize q)).tail he'
  let a := t.first.src
  let b' := t.first.dst
  let c' := t.second.src
  let d := t.second.dst
  let mid := t.second.before
  have hl : ∀ z ∈ vertices mid, f z = f c' :=
    twoSplit_middle_can_be_shortened f hf p b c (vertices (StutterTrace.normalize q)).tail he'
  have htri : ({f a,f c',f d} : Finset W) ∈ B :=
    twoSplit_target_triangle f hf p b c (vertices (StutterTrace.normalize q)).tail he' ht
  refine ⟨blockComplex A a b' c' d mid,block_inclusion A a b' c' d mid,
    block_face_map f hf a b' c' d mid hl htri,
    blockUpper A a b' c' d mid t.first.before t.second.suffix,?_,?_,
    block_vertex_old A a b' c' d mid t.first.face t.second.face,
    block_dimension A a b' c' d mid,
    fun g hs => block_span A a b' c' d mid t.first.face t.second.face g hs⟩
  · have hm := block_moves A a b' c' d mid t.first.face t.second.face t.first.before t.second.suffix
    have hp := twoSplit_decomposition f hf p b c (vertices (StutterTrace.normalize q)).tail he'
    have heq := congrArg (mapPath id (identity_face_map (block_inclusion A a b' c' d mid))) hp
    exact heq.symm ▸ hm
  · apply vertices_injective
    have hp : ∀ z ∈ vertices t.first.before, f z = f a := fun z hz =>
      (t.first.before_labels z hz).trans t.first.src_label.symm
    have hq : vertices (imageTrace f hf t.second.suffix) = vertices (StutterTrace.normalize q) :=
      t.second.suffix_trace.trans (vertices_eq_start_tail (StutterTrace.normalize q)).symm
    change vertices (imageTrace f _ _) = vertices (StutterTrace.normalize (.cons _ q))
    rw [blockUpper_trace f hf a b' c' d mid hl htri _ _ hp,hq,normalize_cons_vertices,
      t.first.src_label,t.second.dst_label]

/-- Adjacent target collapses already have the same normalized trace. -/
theorem collapsed_triangle_trace {B : PreAbstractSimplicialComplex W} {a b c v : W}
    (ht : ({a,b,c} : Finset W) ∈ B) (q : Path B c v) (hc : a = b ∨ b = c) :
    StutterTrace.normalize (.cons (pair_mem_of_face _ _ ht a b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) q)) =
    StutterTrace.normalize (.cons (pair_mem_of_face _ _ ht a c (by simp) (by simp)) q) := by
  rcases hc with rfl | rfl <;> simp [StutterTrace.normalize]

/-- All target triangle deletions at the head, including collapse and backtracking. -/
def deleteHead {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (b c : W) (ht : ({f u,b,c} : Finset W) ∈ B) (q : Path B c (f v))
    (h : Realizes f hf p (.cons (pair_mem_of_face _ _ ht (f u) b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) q))) :
    Deletion f p (.cons (pair_mem_of_face _ _ ht (f u) c (by simp) (by simp)) q) := by
  by_cases hab : f u = b
  · refine ⟨A,le_rfl,hf,p,?_,?_,fun x => x.property,fun hd => hd,?_⟩
    · rw [included_path_identity (le_refl A) p]; exact .refl p
    · exact h.trans (collapsed_triangle_trace ht q (Or.inl hab))
    · intro r g hs
      exact (congrArg (fun p => CycleSpan A (PathChains.chain (PathChains.trivialTransport A) p))
        (included_path_identity (le_refl A) g)).mpr hs
  by_cases hbc : b = c
  · refine ⟨A,le_rfl,hf,p,?_,?_,fun x => x.property,fun hd => hd,?_⟩
    · rw [included_path_identity (le_refl A) p]; exact .refl p
    · exact h.trans (collapsed_triangle_trace ht q (Or.inr hbc))
    · intro r g hs
      exact (congrArg (fun p => CycleSpan A (PathChains.chain (PathChains.trivialTransport A) p))
        (included_path_identity (le_refl A) g)).mpr hs
  apply deleteTwo f hf p b c q _ ht
  have hv := congrArg vertices h
  rw [normalize_cons_vertices,ite_eq_right hab,normalize_cons_vertices,ite_eq_right hbc] at hv
  exact hv


theorem realizes_append {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u x v : V} (pre : Path A u x) (p : Path A x v)
    (tpre : Path B (f u) (f x)) (q : Path B (f x) (f v))
    (hpre : Realizes f hf pre tpre) (hp : Realizes f hf p q) :
    Realizes f hf (append pre p) (append tpre q) := by
  change StutterTrace.normalize (mapPath f hf (append pre p)) = _
  rw [mapPath_append,normalize_append_left,normalize_append_right]
  change StutterTrace.normalize (append (imageTrace f hf pre) (imageTrace f hf p)) = _
  rw [hpre,hp]
  rw [← normalize_append_right,← normalize_append_left]

/-- Prefix wrapping transports an already constructed update, without a new source. -/
def inContext {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u x v : V} (pre : Path A u x) (p : Path A x v)
    (tpre : Path B (f u) (f x)) (q : Path B (f x) (f v))
    (hpre : Realizes f hf pre tpre) (s : Deletion f p q) : Deletion f (append pre p) (append tpre q) := by
  have hr {i j : V} (h : Path A i j) :
      mapPath f s.face_map (mapPath id (identity_face_map s.inclusion) h) = mapPath f hf h := by
    induction h with
    | refl => rfl
    | cons h p ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih
  refine ⟨s.complex,s.inclusion,s.face_map,append (mapPath id (identity_face_map s.inclusion) pre) s.upper,
    ?_,?_,s.vertex_old,s.dimension,s.span⟩
  · rw [mapPath_append]; exact prefixMoves _ s.moves
  · apply realizes_append
    · exact (congrArg StutterTrace.normalize (hr pre)).trans hpre
    · exact s.realizes

def castStart {B : PreAbstractSimplicialComplex W} {a a' v : W}
    (e : a = a') (p : Path B a v) : Path B a' v := e ▸ p

def castEnd {B : PreAbstractSimplicialComplex W} {u a a' : W}
    (e : a = a') (p : Path B u a) : Path B u a' := e ▸ p

theorem normalize_castStart_vertices {B : PreAbstractSimplicialComplex W} {a a' v : W}
    (e : a = a') (p : Path B a v) :
    vertices (StutterTrace.normalize (castStart e p)) = vertices (StutterTrace.normalize p) := by cases e; rfl

theorem normalize_castEnd_vertices {B : PreAbstractSimplicialComplex W} {u a a' : W}
    (e : a = a') (p : Path B u a) :
    vertices (StutterTrace.normalize (castEnd e p)) = vertices (StutterTrace.normalize p) := by cases e; rfl

theorem castStart_cons {B : PreAbstractSimplicialComplex W} {a a' b v : W}
    (e : a = a') (h : ({a,b} : Finset W) ∈ B) (h' : ({a',b} : Finset W) ∈ B) (p : Path B b v) :
    castStart e (.cons h p) = .cons h' p := by cases e; rfl

theorem append_cast {B : PreAbstractSimplicialComplex W} {u a a' v : W}
    (e : a = a') (pre : Path B u a) (post : Path B a v) :
    append (castEnd e pre) (castStart e post) = append pre post := by cases e; rfl

theorem cut_before_realizes {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (a : W)
    (pre : Path B (f u) a) (post : Path B a (f v)) (h : Realizes f hf p (append pre post)) :
    let t := cutAtTargetContext f hf p a pre post h
    Realizes f hf t.before (castEnd t.node_label.symm pre) := by
  apply vertices_injective
  rw [normalize_castEnd_vertices]
  exact cutAtTargetContext_before_trace f hf p a pre post h

theorem cut_after_realizes {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (a : W)
    (pre : Path B (f u) a) (post : Path B a (f v)) (h : Realizes f hf p (append pre post)) :
    let t := cutAtTargetContext f hf p a pre post h
    Realizes f hf t.after (castStart t.node_label.symm post) := by
  apply vertices_injective
  rw [normalize_castStart_vertices]
  exact (cutAtTargetContext f hf p a pre post h).after_trace.trans
    (vertices_eq_start_tail (StutterTrace.normalize post)).symm

/-- ONE arbitrary contextual target triangle deletion is now simulated from Realizes.
The matching source prefix/block is computed, not supplied as a lifting assumption. -/
def deleteContext {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (a b c : W) (ht : ({a,b,c} : Finset W) ∈ B)
    (pre : Path B (f u) a) (post : Path B c (f v))
    (h : Realizes f hf p (append pre (.cons (pair_mem_of_face _ _ ht a b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)))) :
    Deletion f p (append pre (.cons (pair_mem_of_face _ _ ht a c (by simp) (by simp)) post)) := by
  let oldTail := Path.cons (pair_mem_of_face _ _ ht a b (by simp) (by simp))
    (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)
  let t := cutAtTargetContext f hf p a pre oldTail h
  have htri : ({f t.node,b,c} : Finset W) ∈ B := by rw [t.node_label]; exact ht
  have ha := cut_after_realizes f hf p a pre oldTail h
  have hc := castStart_cons t.node_label.symm (pair_mem_of_face _ _ ht a b (by simp) (by simp))
    (pair_mem_of_face _ _ htri (f t.node) b (by simp) (by simp))
    (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)
  have ha' : Realizes f hf t.after (.cons (pair_mem_of_face _ _ htri (f t.node) b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ htri b c (by simp) (by simp)) post)) :=
    ha.trans (congrArg StutterTrace.normalize hc)
  let inner := deleteHead f hf t.after b c htri post ha'
  let wrapped := inContext f hf t.before t.after (castEnd t.node_label.symm pre)
    (.cons (pair_mem_of_face _ _ htri (f t.node) c (by simp) (by simp)) post)
    (cut_before_realizes f hf p a pre oldTail h) inner
  have hsource := congrArg (mapPath id (identity_face_map wrapped.inclusion)) t.decomposition
  have htarget : append (castEnd t.node_label.symm pre)
      (.cons (pair_mem_of_face _ _ htri (f t.node) c (by simp) (by simp)) post) =
      append pre (.cons (pair_mem_of_face _ _ ht a c (by simp) (by simp)) post) :=
    (congrArg (append (castEnd t.node_label.symm pre))
      (castStart_cons t.node_label.symm (pair_mem_of_face _ _ ht a c (by simp) (by simp))
        (pair_mem_of_face _ _ htri (f t.node) c (by simp) (by simp)) post).symm).trans
      (append_cast t.node_label.symm pre (.cons (pair_mem_of_face _ _ ht a c (by simp) (by simp)) post))
  refine ⟨wrapped.complex,wrapped.inclusion,wrapped.face_map,wrapped.upper,?_,?_,
    wrapped.vertex_old,wrapped.dimension,wrapped.span⟩
  · exact hsource.symm ▸ wrapped.moves
  · exact wrapped.realizes.trans (congrArg StutterTrace.normalize htarget)

/-- Backtracks are degenerate target triangles; SOURCE endpoints are not merged. -/
def deleteBacktrack {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (a b : W) (hab : ({a,b} : Finset W) ∈ B)
    (pre : Path B (f u) a) (post : Path B a (f v))
    (h : Realizes f hf p (append pre (.cons hab (.cons (by simpa only [Finset.pair_comm] using hab) post)))) :
    Deletion f p (append pre post) := by
  have he : ({a,b,a} : Finset W) = {a,b} := by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  have ht : ({a,b,a} : Finset W) ∈ B := by rw [he]; exact hab
  let s := deleteContext f hf p a b a ht pre post h
  have he : StutterTrace.normalize (append pre (.cons (pair_mem_of_face _ _ ht a a (by simp) (by simp)) post)) =
      StutterTrace.normalize (append pre post) := by
    apply normalize_prefix_congr
    simp [StutterTrace.normalize]
  exact ⟨s.complex,s.inclusion,s.face_map,s.upper,s.moves,s.realizes.trans he,
    s.vertex_old,s.dimension,s.span⟩

/-- Target stutter deletion requires no SOURCE endpoint identification or extension. -/
def deleteStutter {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (a : W) (ha : ({a} : Finset W) ∈ B)
    (pre : Path B (f u) a) (post : Path B a (f v))
    (h : Realizes f hf p (append pre (.cons (by simpa using ha) post))) :
    Deletion f p (append pre post) := by
  have he : StutterTrace.normalize (append pre (.cons (by simpa using ha) post)) =
      StutterTrace.normalize (append pre post) := by
    apply normalize_prefix_congr
    simp [StutterTrace.normalize]
  refine ⟨A,le_rfl,hf,p,?_,h.trans he,fun x => x.property,fun hd => hd,?_⟩
  · rw [included_path_identity (le_refl A) p]; exact .refl p
  · intro r g hs
    exact (congrArg (fun p => CycleSpan A (PathChains.chain (PathChains.trivialTransport A) p))
      (included_path_identity (le_refl A) g)).mpr hs

/-- An existing SOURCE square-to-upper stage is retained, not assumed null. -/
def squareStage {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {r : V} (g p : Path A r r) (q : Path B (f r) (f r))
    (s : Deletion f p q) (m : Moves (append g g) p) :
    Moves (append (mapPath id (identity_face_map s.inclusion) g)
      (mapPath id (identity_face_map s.inclusion) g)) s.upper := by
  have hm := mapMoves id (identity_face_map s.inclusion) m
  rw [mapPath_append] at hm
  exact .trans hm s.moves

def verticesEquiv {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (s : Deletion f p q) :
    Vertex s.complex ≃ Vertex A where
  toFun x := ⟨x.val,s.vertex_old x⟩
  invFun := vertexInclusion s.inclusion
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem source_count {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (s : Deletion f p q) :
    Nat.card (Vertex s.complex) = Nat.card (Vertex A) := Nat.card_congr (verticesEquiv f p q s)

theorem source_finite {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (s : Deletion f p q) :
    Finite (Vertex s.complex) := Finite.of_equiv _ (verticesEquiv f p q s).symm

def sourcePaths {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (s : Deletion f p q)
    (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val) (x : Vertex s.complex) :
    Path s.complex r.val x.val := mapPath id (identity_face_map s.inclusion) (paths ⟨x.val,s.vertex_old x⟩)

theorem retained_path {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (q : Path B (f u) (f v))
    (s : Deletion f p q) {i j : V} (g : Path A i j) :
    mapPath f s.face_map (mapPath id (identity_face_map s.inclusion) g) = mapPath f hf g := by
  induction g with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih

theorem retained_value {K : Type*} [Field K] {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B)
    {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (s : Deletion f p q)
    {i j : V} (g : Path A i j) :
    value tau (mapPath f s.face_map (mapPath id (identity_face_map s.inclusion) g)) = value tau (mapPath f hf g) :=
  congrArg (value tau) (retained_path f hf p q s g)

def demoMid : Path (PolygonSource.polygon 3) 2 3 := single
  (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 2)

def demoSource := blockComplex (PolygonSource.polygon 3) 1 2 3 4 demoMid

def demoUpper := blockUpper (PolygonSource.polygon 3) 1 2 3 4 demoMid
  (single (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 0))
  (single (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 4))

theorem demo_actual_shortcut : vertices demoUpper = [0,1,4,5] := rfl

theorem missing_target_triangle_rejected :
    ¬ (blockComplex cycleComplex 0 1 1 2 (.refl 1 (by constructor <;> simp))).map
      (id : Fin 3 → Fin 3) ≤ cycleComplex := by
  intro hf
  have hh := image_mem id hf _ (triangle_face (attachment cycleComplex 0 1 1) 0 1 2)
  have ht : ({0,1,2} : Finset (Fin 3)) ∈ cycleComplex := by
    simpa [blockComplex,cap] using hh
  have hc := ht.2
  norm_num at hc

def backtrackLabels (x : Fin 3) : Fin 2 := ⟨x.val % 2,Nat.mod_lt _ (by decide)⟩

theorem backtrack_face_map : cycleComplex.map backtrackLabels ≤ (⊤ : PreAbstractSimplicialComplex (Fin 2)) := by
  rintro s ⟨t,ht,rfl⟩; exact ht.1.image _

def backtrackSource : Path cycleComplex 0 2 :=
  .cons (v := 1) (by constructor <;> simp) (.cons (by constructor <;> simp) (.refl 2 (by constructor <;> simp)))

def backtrackUpdate := deleteBacktrack backtrackLabels backtrack_face_map backtrackSource 0 1
  (B := (⊤ : PreAbstractSimplicialComplex (Fin 2))) (Finset.insert_nonempty _ _)
  (.refl 0 (Finset.singleton_nonempty _)) (.refl 0 (Finset.singleton_nonempty _)) (by rfl)

theorem backtrack_retains_distinct_source_endpoints :
    vertices backtrackUpdate.upper = [0,2] ∧ (0 : Fin 3) ≠ 2 ∧
    PolygonSource.length (imageTrace backtrackLabels backtrackUpdate.face_map backtrackUpdate.upper) = 0 := by
  constructor
  · decide
  constructor
  · decide
  · decide

def collapsedUpdate := deleteHead (id : Fin 3 → Fin 3)
  (B := (⊤ : PreAbstractSimplicialComplex (Fin 3)))
  (by rintro s ⟨t,ht,rfl⟩; exact ht.1.image _) CollapsedSegments.distinctSegment
  0 1 (Finset.insert_nonempty _ _) (.refl 1 (Finset.singleton_nonempty _)) (by rfl)

theorem collapsed_update_retains_source :
    collapsedUpdate.complex = cycleComplex ∧ vertices collapsedUpdate.upper = [0,1] := by
  constructor <;> rfl

theorem wrong_shortcut_endpoint_rejected : vertices demoUpper ≠ [0,1,3,5] := by rw [demo_actual_shortcut]; decide

theorem scalar_agreement_does_not_give_Realizes :
    value (PathChains.trivialTransport (K := ℚ) cycleComplex) cycleLoop = 1 ∧
    ¬ Realizes (id : Fin 3 → Fin 3) (identity_face_map (le_refl cycleComplex))
      cycleLoop (.refl 0 cycleBase.property) := by
  constructor
  · exact IntegerHeights.trivial_value cycleLoop
  · intro h
    have hh := congrArg PolygonSource.length h
    norm_num [Realizes,imageTrace,mapPath,StutterTrace.normalize,cycleLoop,PolygonSource.length] at hh

/-- A triangle deletion may change the normalized trace: retaining the old upper fails. -/
theorem stale_upper_trace_rejected :
    ¬ Realizes demoLabels demo_face_map demoPath
      (single (A := (⊤ : PreAbstractSimplicialComplex (Fin 3))) (u := demoLabels 0) (v := demoLabels 5)
        (Finset.insert_nonempty _ _)) := by
  intro h
  have hh := congrArg vertices h
  rw [demo_trace] at hh
  change [0,1,2] = [0,2] at hh
  contradiction


end D2RelationGap.TriangleTraceUpdate
