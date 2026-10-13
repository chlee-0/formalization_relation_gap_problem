import D2RelationGap.VoltageChains
import D2RelationGap.SimplicialImages

/-!
Ordered cells of actual abstract simplicial complexes and their weighted chains.
OpenAI's "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, Section 2,
supplies the tower argument. Geometric/local-system and voltage-cover cell
comparisons are still separate obligations; no full obstruction is asserted.
-/

noncomputable section
namespace D2RelationGap.OrientedSimplices

variable {V K : Type*} [LinearOrder V] [Field K]

abbrev Vertex (A : PreAbstractSimplicialComplex V) := {v : V // {v} ∈ A}

@[ext]
structure Edge (A : PreAbstractSimplicialComplex V) where
  src : V
  dst : V
  ordered : src < dst
  face : ({src, dst} : Finset V) ∈ A

@[ext]
structure Triangle (A : PreAbstractSimplicialComplex V) where
  v0 : V
  v1 : V
  v2 : V
  ordered01 : v0 < v1
  ordered12 : v1 < v2
  face : ({v0, v1, v2} : Finset V) ∈ A

theorem pair_mem_of_face (A : PreAbstractSimplicialComplex V) (s : Finset V)
    (hs : s ∈ A) (u v : V) (hu : u ∈ s) (hv : v ∈ s) : ({u, v} : Finset V) ∈ A :=
  (A.isRelLowerSet_faces hs).2
    (Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩)
    (Finset.insert_nonempty _ _)

omit [LinearOrder V] in
theorem vertex_mem_of_face (A : PreAbstractSimplicialComplex V) (s : Finset V)
    (hs : s ∈ A) (v : V) (hv : v ∈ s) : ({v} : Finset V) ∈ A :=
  (A.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty _)

def face01 {A : PreAbstractSimplicialComplex V} (t : Triangle A) : Edge A where
  src := t.v0
  dst := t.v1
  ordered := t.ordered01
  face := pair_mem_of_face A _ t.face _ _ (by simp) (by simp)

def face02 {A : PreAbstractSimplicialComplex V} (t : Triangle A) : Edge A where
  src := t.v0
  dst := t.v2
  ordered := lt_trans t.ordered01 t.ordered12
  face := pair_mem_of_face A _ t.face _ _ (by simp) (by simp)

def face12 {A : PreAbstractSimplicialComplex V} (t : Triangle A) : Edge A where
  src := t.v1
  dst := t.v2
  ordered := t.ordered12
  face := pair_mem_of_face A _ t.face _ _ (by simp) (by simp)

/-- The incidence data is constructed from the actual ordered faces. Degree
zero uses active vertices, rather than all vertices of the ambient type. -/
def incidence (A : PreAbstractSimplicialComplex V) :
    VoltageChains.TwoComplex (Vertex A) (Edge A) (Triangle A) where
  src e := ⟨e.src, vertex_mem_of_face A _ e.face _ (by simp)⟩
  dst e := ⟨e.dst, vertex_mem_of_face A _ e.face _ (by simp)⟩
  edge01 := face01
  edge02 := face02
  edge12 := face12
  first _ := Subtype.ext rfl
  middle _ := Subtype.ext rfl
  last _ := Subtype.ext rfl

def boundaryOne (A : PreAbstractSimplicialComplex V) (lambda : V → V → K) :
    (Edge A →₀ K) →ₗ[K] Vertex A →₀ K :=
  VoltageChains.baseOne (incidence A) (fun e => lambda e.src e.dst)

def boundaryTwo (A : PreAbstractSimplicialComplex V) (lambda : V → V → K) :
    (Triangle A →₀ K) →ₗ[K] Edge A →₀ K :=
  VoltageChains.baseTwo (incidence A) (fun e => lambda e.src e.dst)

theorem boundaryTwo_single (A : PreAbstractSimplicialComplex V)
    (lambda : V → V → K) (t : Triangle A) (c : K) :
    boundaryTwo A lambda (Finsupp.single t c) =
      c • (lambda t.v0 t.v1 • Finsupp.single (face12 t) 1 -
        Finsupp.single (face02 t) 1 + Finsupp.single (face01 t) 1) := by
  simp [boundaryTwo, VoltageChains.baseTwo, incidence, face01]

theorem boundary_chain (A : PreAbstractSimplicialComplex V) (lambda : V → V → K)
    (hl : ∀ t : Triangle A, lambda t.v0 t.v1 * lambda t.v1 t.v2 = lambda t.v0 t.v2) :
    (boundaryOne A lambda).comp (boundaryTwo A lambda) = 0 := by
  apply Finsupp.lhom_ext
  intro t c
  simp [boundaryOne, boundaryTwo, VoltageChains.baseOne, VoltageChains.baseTwo,
    incidence, face01, face02, face12, mul_assoc, hl, smul_sub]

def vertexInclusion {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (v : Vertex A) : Vertex B := ⟨v.val, hAB v.property⟩

def edgeInclusion {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (e : Edge A) : Edge B := ⟨e.src, e.dst, e.ordered, hAB e.face⟩

def triangleInclusion {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (t : Triangle A) : Triangle B :=
  ⟨t.v0, t.v1, t.v2, t.ordered01, t.ordered12, hAB t.face⟩

omit [LinearOrder V] in
theorem vertexInclusion_injective {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Function.Injective (vertexInclusion hAB) := by
  intro u v h
  exact Subtype.ext (congrArg (fun v : Vertex B => v.val) h)

theorem edgeInclusion_injective {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Function.Injective (edgeInclusion hAB) := by
  intro e f h
  exact Edge.ext (congrArg (fun e : Edge B => e.src) h)
    (congrArg (fun e : Edge B => e.dst) h)

theorem triangleInclusion_injective {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Function.Injective (triangleInclusion hAB) := by
  intro t u h
  exact Triangle.ext (congrArg (fun t : Triangle B => t.v0) h)
    (congrArg (fun t : Triangle B => t.v1) h) (congrArg (fun t : Triangle B => t.v2) h)

def includeVertices {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    (Vertex A →₀ K) →ₗ[K] Vertex B →₀ K :=
  Finsupp.lmapDomain K K (vertexInclusion hAB)

def includeEdges {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    (Edge A →₀ K) →ₗ[K] Edge B →₀ K := Finsupp.lmapDomain K K (edgeInclusion hAB)

def includeTriangles {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    (Triangle A →₀ K) →ₗ[K] Triangle B →₀ K :=
  Finsupp.lmapDomain K K (triangleInclusion hAB)

theorem includeEdges_injective {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Function.Injective (includeEdges (K := K) hAB) :=
  Finsupp.mapDomain_injective (edgeInclusion_injective hAB)

theorem includeTriangles_injective {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Function.Injective (includeTriangles (K := K) hAB) :=
  Finsupp.mapDomain_injective (triangleInclusion_injective hAB)

theorem inclusion_boundary_one {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (lambda : V → V → K) :
    (includeVertices hAB).comp (boundaryOne A lambda) =
      (boundaryOne B lambda).comp (includeEdges hAB) := by
  apply Finsupp.lhom_ext
  intro e c
  simp [includeVertices, includeEdges, boundaryOne, VoltageChains.baseOne,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub, incidence, vertexInclusion,
    edgeInclusion]

theorem inclusion_boundary_two {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (lambda : V → V → K) :
    (includeEdges hAB).comp (boundaryTwo A lambda) =
      (boundaryTwo B lambda).comp (includeTriangles hAB) := by
  apply Finsupp.lhom_ext
  intro t c
  simp [includeEdges, includeTriangles, boundaryTwo, VoltageChains.baseTwo,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub, Finsupp.mapDomain_add,
    Finsupp.mapDomain_smul, incidence, triangleInclusion, edgeInclusion,
    face01, face02, face12]

/-- Degree-two injectivity for a literal abstract simplicial subcomplex. -/
theorem subcomplex_two_injective {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    (lambda : V → V → K) (h : Function.Injective (boundaryTwo B lambda)) :
    Function.Injective (boundaryTwo A lambda) := by
  intro x y hxy
  apply includeTriangles_injective hAB
  apply h
  have hx := LinearMap.congr_fun (inclusion_boundary_two hAB lambda) x
  have hy := LinearMap.congr_fun (inclusion_boundary_two hAB lambda) y
  exact hx.symm.trans ((congrArg (includeEdges hAB) hxy).trans hy)

def edgeFace {A : PreAbstractSimplicialComplex V} (e : Edge A) : Finset V :=
  {e.src, e.dst}

def triangleFace {A : PreAbstractSimplicialComplex V} (t : Triangle A) : Finset V :=
  {t.v0, t.v1, t.v2}

/-- The actual cell subsets of A inside the ordered incidence model of B.
For arbitrary A,B this is their intersection; A ≤ B makes it precisely A. -/
def incidenceSubcomplex (A B : PreAbstractSimplicialComplex V) :
    VoltageChains.Subcomplex (incidence B) where
  vertices := {v | {v.val} ∈ A}
  edges := {e | edgeFace e ∈ A}
  triangles := {t | triangleFace t ∈ A}
  src_mem e he := vertex_mem_of_face A _ he _ (by simp [edgeFace, incidence])
  dst_mem e he := vertex_mem_of_face A _ he _ (by simp [edgeFace, incidence])
  edge01_mem t ht := pair_mem_of_face A _ ht _ _ (by simp [triangleFace, incidence, face01])
    (by simp [triangleFace, incidence, face01])
  edge02_mem t ht := pair_mem_of_face A _ ht _ _ (by simp [triangleFace, incidence, face02])
    (by simp [triangleFace, incidence, face02])
  edge12_mem t ht := pair_mem_of_face A _ ht _ _ (by simp [triangleFace, incidence, face12])
    (by simp [triangleFace, incidence, face12])

def edgeSubcomplexEquiv {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Edge A ≃ (incidenceSubcomplex A B).edges where
  toFun e := ⟨edgeInclusion hAB e, e.face⟩
  invFun e := ⟨e.val.src, e.val.dst, e.val.ordered, e.property⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨⟨_, _, _, _⟩, _⟩; rfl

def triangleSubcomplexEquiv {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    Triangle A ≃ (incidenceSubcomplex A B).triangles where
  toFun t := ⟨triangleInclusion hAB t, t.face⟩
  invFun t := ⟨t.val.v0, t.val.v1, t.val.v2, t.val.ordered01, t.val.ordered12, t.property⟩
  left_inv t := by cases t; rfl
  right_inv t := by rcases t with ⟨⟨_, _, _, _, _, _⟩, _⟩; rfl

theorem includeEdges_eq_extend {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    includeEdges (K := K) hAB =
      (VoltageChains.extend (incidenceSubcomplex A B).edges).comp
        (Finsupp.domLCongr (edgeSubcomplexEquiv hAB)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro e c
  simp [includeEdges, VoltageChains.extend, Finsupp.lmapDomain_apply,
    Finsupp.domLCongr, edgeSubcomplexEquiv]

theorem includeTriangles_eq_extend {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B) :
    includeTriangles (K := K) hAB =
      (VoltageChains.extend (incidenceSubcomplex A B).triangles).comp
        (Finsupp.domLCongr (triangleSubcomplexEquiv hAB)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro t c
  simp [includeTriangles, VoltageChains.extend, Finsupp.lmapDomain_apply,
    Finsupp.domLCongr, triangleSubcomplexEquiv]

theorem edgeFace_card {A : PreAbstractSimplicialComplex V} (e : Edge A) :
    (edgeFace e).card = 2 := by simp [edgeFace, e.ordered.ne]

theorem triangleFace_card {A : PreAbstractSimplicialComplex V} (t : Triangle A) :
    (triangleFace t).card = 3 := by
  simp [triangleFace, t.ordered01.ne, t.ordered12.ne,
    (lt_trans t.ordered01 t.ordered12).ne]

theorem edgeFace_injective {A : PreAbstractSimplicialComplex V} :
    Function.Injective (edgeFace (A := A)) := by
  intro e f h
  have lo (e : Edge A) (x : V) (hx : x ∈ edgeFace e) : e.src ≤ x := by
    rcases (by simpa [edgeFace] using hx : x = e.src ∨ x = e.dst) with rfl | rfl
    · exact le_rfl
    · exact e.ordered.le
  have hi (e : Edge A) (x : V) (hx : x ∈ edgeFace e) : x ≤ e.dst := by
    rcases (by simpa [edgeFace] using hx : x = e.src ∨ x = e.dst) with rfl | rfl
    · exact e.ordered.le
    · exact le_rfl
  apply Edge.ext
  · exact le_antisymm (lo e f.src (by rw [h]; simp [edgeFace]))
      (lo f e.src (by rw [← h]; simp [edgeFace]))
  · exact le_antisymm (hi f e.dst (by rw [← h]; simp [edgeFace]))
      (hi e f.dst (by rw [h]; simp [edgeFace]))

theorem triangleFace_injective {A : PreAbstractSimplicialComplex V} :
    Function.Injective (triangleFace (A := A)) := by
  intro t u h
  have lo (t : Triangle A) (x : V) (hx : x ∈ triangleFace t) : t.v0 ≤ x := by
    rcases (by simpa [triangleFace] using hx : x = t.v0 ∨ x = t.v1 ∨ x = t.v2)
      with rfl | rfl | rfl
    · exact le_rfl
    · exact t.ordered01.le
    · exact (lt_trans t.ordered01 t.ordered12).le
  have hi (t : Triangle A) (x : V) (hx : x ∈ triangleFace t) : x ≤ t.v2 := by
    rcases (by simpa [triangleFace] using hx : x = t.v0 ∨ x = t.v1 ∨ x = t.v2)
      with rfl | rfl | rfl
    · exact (lt_trans t.ordered01 t.ordered12).le
    · exact t.ordered12.le
    · exact le_rfl
  have h0 : t.v0 = u.v0 := le_antisymm
    (lo t u.v0 (by rw [h]; simp [triangleFace]))
    (lo u t.v0 (by rw [← h]; simp [triangleFace]))
  have h2 : t.v2 = u.v2 := le_antisymm
    (hi u t.v2 (by rw [← h]; simp [triangleFace]))
    (hi t u.v2 (by rw [h]; simp [triangleFace]))
  have hm : u.v1 = t.v0 ∨ u.v1 = t.v1 ∨ u.v1 = t.v2 := by
    have hh : u.v1 ∈ triangleFace t := by rw [h]; simp [triangleFace]
    simpa [triangleFace] using hh
  refine Triangle.ext h0 ?_ h2
  rcases hm with hm | hm | hm
  · have hh := u.ordered01
    rw [← h0, hm] at hh
    exact (lt_irrefl _ hh).elim
  · exact hm.symm
  · have hh := u.ordered12
    rw [← h2, hm] at hh
    exact (lt_irrefl _ hh).elim

theorem edge_of_face_card_two (A : PreAbstractSimplicialComplex V) (s : Finset V)
    (hs : s ∈ A) (hc : s.card = 2) : ∃ e : Edge A, edgeFace e = s := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact ⟨⟨u, v, hlt, hs⟩, rfl⟩
  · refine ⟨⟨v, u, hgt, by simpa [Finset.pair_comm] using hs⟩, ?_⟩
    simp [edgeFace, Finset.pair_comm]

theorem triangle_of_face_card_three (A : PreAbstractSimplicialComplex V) (s : Finset V)
    (hs : s ∈ A) (hc : s.card = 3) : ∃ t : Triangle A, triangleFace t = s := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hc
  rcases lt_or_gt_of_ne huv with huv | hvu
  · rcases lt_or_gt_of_ne hvw with hvw | hwv
    · exact ⟨⟨u, v, w, huv, hvw, hs⟩, rfl⟩
    · rcases lt_or_gt_of_ne huw with huw | hwu
      · refine ⟨⟨u, w, v, huw, hwv, ?_⟩, ?_⟩
        · convert hs using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; aesop
        · ext x; simp only [triangleFace, Finset.mem_insert, Finset.mem_singleton]; aesop
      · refine ⟨⟨w, u, v, hwu, huv, ?_⟩, ?_⟩
        · convert hs using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; aesop
        · ext x; simp only [triangleFace, Finset.mem_insert, Finset.mem_singleton]; aesop
  · rcases lt_or_gt_of_ne huw with huw | hwu
    · refine ⟨⟨v, u, w, hvu, huw, ?_⟩, ?_⟩
      · convert hs using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; aesop
      · ext x; simp only [triangleFace, Finset.mem_insert, Finset.mem_singleton]; aesop
    · rcases lt_or_gt_of_ne hvw with hvw | hwv
      · refine ⟨⟨v, w, u, hvw, hwu, ?_⟩, ?_⟩
        · convert hs using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; aesop
        · ext x; simp only [triangleFace, Finset.mem_insert, Finset.mem_singleton]; aesop
      · refine ⟨⟨w, v, u, hwv, hvu, ?_⟩, ?_⟩
        · convert hs using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; aesop
        · ext x; simp only [triangleFace, Finset.mem_insert, Finset.mem_singleton]; aesop

abbrev FaceOfCard (A : PreAbstractSimplicialComplex V) (n : ℕ) :=
  {s : Finset V // s ∈ A ∧ s.card = n}

def edgeFaceEquiv (A : PreAbstractSimplicialComplex V) : Edge A ≃ FaceOfCard A 2 :=
  Equiv.ofBijective (fun e => ⟨edgeFace e, e.face, edgeFace_card e⟩) (by
    constructor
    · intro e f h
      exact edgeFace_injective (congrArg (fun s : FaceOfCard A 2 => s.val) h)
    · rintro ⟨s, hs, hc⟩
      obtain ⟨e, he⟩ := edge_of_face_card_two A s hs hc
      exact ⟨e, Subtype.ext he⟩)

def triangleFaceEquiv (A : PreAbstractSimplicialComplex V) : Triangle A ≃ FaceOfCard A 3 :=
  Equiv.ofBijective (fun t => ⟨triangleFace t, t.face, triangleFace_card t⟩) (by
    constructor
    · intro t u h
      exact triangleFace_injective (congrArg (fun s : FaceOfCard A 3 => s.val) h)
    · rintro ⟨s, hs, hc⟩
      obtain ⟨t, ht⟩ := triangle_of_face_card_three A s hs hc
      exact ⟨t, Subtype.ext ht⟩)

def edgeChainsEquiv (A : PreAbstractSimplicialComplex V) :
    (Edge A →₀ K) ≃ₗ[K] FaceOfCard A 2 →₀ K :=
  Finsupp.domLCongr (edgeFaceEquiv A)

def triangleChainsEquiv (A : PreAbstractSimplicialComplex V) :
    (Triangle A →₀ K) ≃ₗ[K] FaceOfCard A 3 →₀ K :=
  Finsupp.domLCongr (triangleFaceEquiv A)

theorem triangleChainsEquiv_single (A : PreAbstractSimplicialComplex V)
    (t : Triangle A) (c : K) :
    triangleChainsEquiv A (Finsupp.single t c) =
      Finsupp.single (triangleFaceEquiv A t) c := by
  simp [triangleChainsEquiv, Finsupp.domLCongr]

/-- The signs are part of the actual ordered-face boundary, not just a
convention on a numerical table. -/
theorem corrupted_middle_face_sign_rejected [CharZero K] :
    let A : PreAbstractSimplicialComplex (Fin 3) := ⊤
    let t : Triangle A := ⟨0, 1, 2, by decide, by decide, Finset.insert_nonempty _ _⟩
    boundaryOne A (fun _ _ => (1 : K))
      (Finsupp.single (face12 t) 1 + Finsupp.single (face02 t) 1 +
        Finsupp.single (face01 t) 1) ≠ 0 := by
  dsimp only
  intro h
  have hc := congrArg (fun c : Vertex (⊤ : PreAbstractSimplicialComplex (Fin 3)) →₀ K =>
    c ⟨2, Finset.singleton_nonempty _⟩) h
  norm_num [boundaryOne, VoltageChains.baseOne, incidence, face01, face02, face12,
    Finsupp.single_apply] at hc

/-- Reversed vertices cannot be used as the positively ordered edge basis. -/
theorem reversed_edge_rejected :
    ¬ ∃ e : Edge (⊤ : PreAbstractSimplicialComplex (Fin 2)), e.src = 1 ∧ e.dst = 0 := by
  rintro ⟨e, hs, hd⟩
  have he := e.ordered
  rw [hs, hd] at he
  exact (by decide : ¬ ((1 : Fin 2) < 0)) he

end D2RelationGap.OrientedSimplices
