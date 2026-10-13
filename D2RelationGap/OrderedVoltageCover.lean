import D2RelationGap.OrientedSimplices
import Mathlib.Data.Prod.Lex

/-!
Ordered cells of the actual abstract voltage complex and their coefficient chains.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, Section 2,
supplies the tower argument. This is an abstract combinatorial adapter;
geometric realization and local-system homology are not asserted.
-/

noncomputable section
namespace D2RelationGap.OrderedVoltageCover
open OrientedSimplices
variable {V K : Type*} [LinearOrder V] [Field K]

/-- Use an explicit order tag; no competing order on the ordinary product. -/
def cover (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ) :
    PreAbstractSimplicialComplex (V ×ₗ ℤ) :=
  (SimplicialImages.voltageComplex A a).map toLex

theorem mem_cover_iff (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (s : Finset (V ×ₗ ℤ)) : s ∈ cover A a ↔
      s.image ofLex ∈ SimplicialImages.voltageComplex A a := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩
    change t ∈ SimplicialImages.voltageComplex A a at ht
    simpa [Finset.image_image, Function.comp_def] using ht
  · intro hs
    refine ⟨s.image ofLex, hs, ?_⟩
    simp [Finset.image_image, Function.comp_def]

theorem height_difference (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (s : Finset (V ×ₗ ℤ)) (hs : s ∈ cover A a)
    (x y : V ×ₗ ℤ) (hx : x ∈ s) (hy : y ∈ s) :
    (ofLex y).2 - (ofLex x).2 = a (ofLex x).1 (ofLex y).1 := by
  exact ((mem_cover_iff A a s).mp hs).2.2 _ (Finset.mem_image_of_mem _ hx)
    _ (Finset.mem_image_of_mem _ hy)

theorem projected_lt (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (s : Finset (V ×ₗ ℤ)) (hs : s ∈ cover A a)
    (x y : V ×ₗ ℤ) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    (ofLex x).1 < (ofLex y).1 := by
  rcases Prod.Lex.lt_iff.mp hxy with h | ⟨h, _⟩
  · exact h
  · have he := SimplicialImages.projection_injective_on_face A a _
      ((mem_cover_iff A a s).mp hs)
      (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy) h
    exact False.elim (ne_of_lt hxy (ofLex.injective he))

/-- The root-based height assignment, including repeated vertices. -/
theorem lifted_face_mem (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (s : Finset V) (hs : s ∈ A)
    (r : V) (hr : r ∈ s) (n : ℤ) :
    s.image (fun v => toLex (v, n + a r v)) ∈ cover A a := by
  classical
  apply (mem_cover_iff A a _).mpr
  simp only [Finset.image_image, ofLex_toLex, Function.comp_def]
  refine ⟨Finset.image_nonempty.mpr (A.isRelLowerSet_faces hs).1, ?_, ?_⟩
  · simpa [Finset.image_image, Function.comp_def] using hs
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hh := ha r u v ((A.isRelLowerSet_faces hs).2
      (Finset.insert_subset_iff.mpr ⟨hr, Finset.insert_subset_iff.mpr
        ⟨hu, Finset.singleton_subset_iff.mpr hv⟩⟩) (Finset.insert_nonempty _ _))
    change (n + a r v) - (n + a r u) = a u v
    omega

theorem diagonal_zero (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (v : Vertex A) : a v.val v.val = 0 := by
  have h := ha v.val v.val v.val (by simpa using v.property)
  omega

def liftVertex (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (vn : Vertex A × ℤ) : Vertex (cover A a) :=
  ⟨toLex (vn.1.val, vn.2), by
    simpa [diagonal_zero A a ha vn.1] using
      lifted_face_mem A a ha {vn.1.val} vn.1.property vn.1.val (by simp) vn.2⟩

def projectVertex (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (v : Vertex (cover A a)) : Vertex A × ℤ :=
  (⟨(ofLex v.val).1, by
    have h := ((mem_cover_iff A a _).mp v.property).2.1
    simpa using h⟩, (ofLex v.val).2)

def vertexEquiv (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) : Vertex (cover A a) ≃ Vertex A × ℤ where
  toFun := projectVertex A a
  invFun := liftVertex A a ha
  left_inv v := Subtype.ext (by simp [liftVertex, projectVertex])
  right_inv vn := by cases vn; rfl

def liftEdge (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (en : Edge A × ℤ) : Edge (cover A a) where
  src := toLex (en.1.src, en.2)
  dst := toLex (en.1.dst, en.2 + a en.1.src en.1.dst)
  ordered := Prod.Lex.toLex_lt_toLex.mpr (Or.inl en.1.ordered)
  face := by
    have hd : a en.1.src en.1.src = 0 :=
      diagonal_zero A a ha ((incidence A).src en.1)
    simpa [incidence, hd] using
      lifted_face_mem A a ha _ en.1.face en.1.src (by simp) en.2

def projectEdge (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (e : Edge (cover A a)) : Edge A × ℤ :=
  (⟨(ofLex e.src).1, (ofLex e.dst).1,
    projected_lt A a _ e.face _ _ (by simp) (by simp) e.ordered, by
      have h := ((mem_cover_iff A a _).mp e.face).2.1
      simpa [Finset.image_image, Function.comp_def] using h⟩, (ofLex e.src).2)

def edgeEquiv (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) : Edge (cover A a) ≃ Edge A × ℤ where
  toFun := projectEdge A a
  invFun := liftEdge A a ha
  left_inv e := by
    apply Edge.ext
    · simp [liftEdge, projectEdge]
    · have hh := height_difference A a _ e.face e.src e.dst (by simp) (by simp)
      apply ofLex.injective
      simp only [liftEdge, projectEdge, ofLex_toLex]
      exact Prod.ext rfl (by omega)
  right_inv en := by cases en; rfl

def liftTriangle (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (tn : Triangle A × ℤ) : Triangle (cover A a) where
  v0 := toLex (tn.1.v0, tn.2)
  v1 := toLex (tn.1.v1, tn.2 + a tn.1.v0 tn.1.v1)
  v2 := toLex (tn.1.v2, tn.2 + a tn.1.v0 tn.1.v2)
  ordered01 := Prod.Lex.toLex_lt_toLex.mpr (Or.inl tn.1.ordered01)
  ordered12 := Prod.Lex.toLex_lt_toLex.mpr (Or.inl tn.1.ordered12)
  face := by
    have hd : a tn.1.v0 tn.1.v0 = 0 :=
      diagonal_zero A a ha ((incidence A).src (face01 tn.1))
    simpa [incidence, face01, hd] using
      lifted_face_mem A a ha _ tn.1.face tn.1.v0 (by simp) tn.2

def projectTriangle (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (t : Triangle (cover A a)) : Triangle A × ℤ :=
  (⟨(ofLex t.v0).1, (ofLex t.v1).1, (ofLex t.v2).1,
    projected_lt A a _ t.face _ _ (by simp) (by simp) t.ordered01,
    projected_lt A a _ t.face _ _ (by simp) (by simp) t.ordered12, by
      have h := ((mem_cover_iff A a _).mp t.face).2.1
      simpa [Finset.image_image, Function.comp_def] using h⟩, (ofLex t.v0).2)

def triangleEquiv (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) : Triangle (cover A a) ≃ Triangle A × ℤ where
  toFun := projectTriangle A a
  invFun := liftTriangle A a ha
  left_inv t := by
    apply Triangle.ext
    · simp [liftTriangle, projectTriangle]
    · have hh := height_difference A a _ t.face t.v0 t.v1 (by simp) (by simp)
      apply ofLex.injective
      exact Prod.ext rfl (by dsimp [liftTriangle, projectTriangle]; omega)
    · have hh := height_difference A a _ t.face t.v0 t.v2 (by simp) (by simp)
      apply ofLex.injective
      exact Prod.ext rfl (by dsimp [liftTriangle, projectTriangle]; omega)
  right_inv tn := by cases tn; rfl



/-- All face heights agree with the incidence voltage cover. In particular,
the 12-face starts at the shifted first endpoint. -/
theorem face12_height (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (tn : Triangle A × ℤ) :
    edgeEquiv A a ha (face12 (liftTriangle A a ha tn)) =
      (face12 tn.1, tn.2 + a tn.1.v0 tn.1.v1) := rfl

theorem face01_height (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (tn : Triangle A × ℤ) :
    edgeEquiv A a ha (face01 (liftTriangle A a ha tn)) = (face01 tn.1, tn.2) := rfl

theorem face02_height (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (tn : Triangle A × ℤ) :
    edgeEquiv A a ha (face02 (liftTriangle A a ha tn)) = (face02 tn.1, tn.2) := rfl

theorem src_height (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (en : Edge A × ℤ) :
    vertexEquiv A a ha ((incidence (cover A a)).src (liftEdge A a ha en)) =
      ((incidence A).src en.1, en.2) := rfl

theorem dst_height (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (en : Edge A × ℤ) :
    vertexEquiv A a ha ((incidence (cover A a)).dst (liftEdge A a ha en)) =
      ((incidence A).dst en.1, en.2 + a en.1.src en.1.dst) := rfl

def vertexChains (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) :
    (Vertex (cover A a) →₀ K) ≃ₗ[K] VoltageChains.LiftChain K (Vertex A) :=
  Finsupp.domLCongr (vertexEquiv A a ha)

def edgeChains (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) :
    (Edge (cover A a) →₀ K) ≃ₗ[K] VoltageChains.LiftChain K (Edge A) :=
  Finsupp.domLCongr (edgeEquiv A a ha)

def triangleChains (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) :
    (Triangle (cover A a) →₀ K) ≃ₗ[K] VoltageChains.LiftChain K (Triangle A) :=
  Finsupp.domLCongr (triangleEquiv A a ha)

/-- Coefficients remain in the fiber based at the first vertex. -/
def pullTransport (lambda : V → V → K) (x y : V ×ₗ ℤ) : K :=
  lambda (ofLex x).1 (ofLex y).1

theorem boundary_one (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (lambda : V → V → K) :
    (vertexChains A a ha).toLinearMap.comp (boundaryOne (cover A a) (pullTransport lambda)) =
      (VoltageChains.liftedOne (incidence A) (fun e => lambda e.src e.dst)
        (fun e => a e.src e.dst)).comp (edgeChains A a ha).toLinearMap := by
  apply Finsupp.lhom_ext
  intro e c
  obtain ⟨en, rfl⟩ := (edgeEquiv A a ha).symm.surjective e
  change vertexChains A a ha (boundaryOne (cover A a) (pullTransport lambda)
    (Finsupp.single (liftEdge A a ha en) c)) = _
  simp [vertexChains, edgeChains, Finsupp.domLCongr, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_sub, boundaryOne, VoltageChains.baseOne,
    VoltageChains.liftedOne, Finsupp.linearCombination_single, liftEdge, pullTransport,
    vertexEquiv, projectVertex, edgeEquiv, projectEdge, incidence]

theorem boundary_two (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (lambda : V → V → K) :
    (edgeChains A a ha).toLinearMap.comp (boundaryTwo (cover A a) (pullTransport lambda)) =
      (VoltageChains.liftedTwo (incidence A) (fun e => lambda e.src e.dst)
        (fun e => a e.src e.dst)).comp (triangleChains A a ha).toLinearMap := by
  apply Finsupp.lhom_ext
  intro t c
  obtain ⟨tn, rfl⟩ := (triangleEquiv A a ha).symm.surjective t
  change edgeChains A a ha (boundaryTwo (cover A a) (pullTransport lambda)
    (Finsupp.single (liftTriangle A a ha tn) c)) = _
  simp [edgeChains, triangleChains, Finsupp.domLCongr, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_sub,
    Finsupp.mapDomain_add, Finsupp.mapDomain_smul, boundaryTwo, VoltageChains.baseTwo,
    VoltageChains.liftedTwo, Finsupp.linearCombination_single, liftTriangle, pullTransport,
    edgeEquiv, projectEdge, triangleEquiv, projectTriangle, incidence, face01, face02, face12]

/-- Finite base cell sets suffice; no connectedness or primitivity is needed. -/
theorem cover_two_injective (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (lambda : V → V → K)
    [Fintype (Edge A)] [Fintype (Triangle A)]
    (hA : Function.Injective (boundaryTwo A lambda)) :
    Function.Injective (boundaryTwo (cover A a) (pullTransport lambda)) := by
  have hi := VoltageChains.lifted_two_injective_of_base_two_injective
    (incidence A) (fun e => lambda e.src e.dst) (fun e => a e.src e.dst) hA
  intro x y hxy
  apply (triangleChains A a ha).injective
  apply hi
  have hx := LinearMap.congr_fun (boundary_two A a ha lambda) x
  have hy := LinearMap.congr_fun (boundary_two A a ha lambda) y
  exact hx.symm.trans ((congrArg (edgeChains A a ha) hxy).trans hy)

theorem subcomplex_two_injective (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (lambda : V → V → K)
    [Fintype (Edge A)] [Fintype (Triangle A)]
    (hA : Function.Injective (boundaryTwo A lambda))
    (B : PreAbstractSimplicialComplex (V ×ₗ ℤ)) (hB : B ≤ cover A a) :
    Function.Injective (boundaryTwo B (pullTransport lambda)) :=
  OrientedSimplices.subcomplex_two_injective hB _ (cover_two_injective A a ha lambda hA)



def edgeLaurentChains (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) :
    (Edge (cover A a) →₀ K) ≃ₗ[K] VoltageChains.OrbitChain K (Edge A) :=
  (edgeChains A a ha).trans (VoltageChains.orbitEquiv (Edge A))

def triangleLaurentChains (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) :
    (Triangle (cover A a) →₀ K) ≃ₗ[K] VoltageChains.OrbitChain K (Triangle A) :=
  (triangleChains A a ha).trans (VoltageChains.orbitEquiv (Triangle A))

theorem triangleLaurentChains_single (A : PreAbstractSimplicialComplex V)
    (a : V → V → ℤ) (ha : SimplicialImages.FlatVoltage A a)
    (tn : Triangle A × ℤ) (c : K) :
    triangleLaurentChains A a ha (Finsupp.single (liftTriangle A a ha tn) c) =
      Finsupp.single tn.1 (LaurentPolynomial.C c * LaurentPolynomial.T tn.2) := by
  simp [triangleLaurentChains, triangleChains, Finsupp.domLCongr,
    triangleEquiv, projectTriangle, liftTriangle, VoltageChains.orbitEquiv_single]

theorem laurent_boundary_two (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (lambda : V → V → K)
    (x : Triangle (cover A a) →₀ K) :
    edgeLaurentChains A a ha (boundaryTwo (cover A a) (pullTransport lambda) x) =
      VoltageChains.laurentTwo (incidence A) (fun e => lambda e.src e.dst)
        (fun e => a e.src e.dst) (triangleLaurentChains A a ha x) := by
  change VoltageChains.orbitEquiv (Edge A)
    (edgeChains A a ha (boundaryTwo (cover A a) (pullTransport lambda) x)) = _
  have hb := LinearMap.congr_fun (boundary_two A a ha lambda) x
  change edgeChains A a ha (boundaryTwo (cover A a) (pullTransport lambda) x) =
    VoltageChains.liftedTwo (incidence A) (fun e => lambda e.src e.dst)
      (fun e => a e.src e.dst) (triangleChains A a ha x) at hb
  rw [hb]
  exact LinearMap.congr_fun (VoltageChains.orbit_boundary_two (incidence A)
    (fun e => lambda e.src e.dst) (fun e => a e.src e.dst)) (triangleChains A a ha x)

/-- The actual tagged height image is a subcomplex of this same ordered cover.
No nondegeneracy or order preservation is imposed on the source map. -/
theorem height_image_le_cover {U : Type*} [DecidableEq U]
    (Source : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (a : V → V → ℤ)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ Source → h v - h u = a (f u) (f v)) :
    Source.map (fun u => toLex (SimplicialImages.heightLift f h u)) ≤ cover (Source.map f) a := by
  rintro s ⟨t, ht, rfl⟩
  apply (mem_cover_iff _ _ _).mpr
  simp only [Finset.image_image, ofLex_toLex, Function.comp_def]
  exact SimplicialImages.height_image_le_voltage Source f h a hh ⟨t, ht, rfl⟩

theorem height_image_two_injective {U : Type*} [DecidableEq U]
    (Source : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (a : V → V → ℤ) (ha : SimplicialImages.FlatVoltage (Source.map f) a)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ Source → h v - h u = a (f u) (f v))
    (lambda : V → V → K) [Fintype (Edge (Source.map f))] [Fintype (Triangle (Source.map f))]
    (hA : Function.Injective (boundaryTwo (Source.map f) lambda)) :
    Function.Injective (boundaryTwo
      (Source.map (fun u => toLex (SimplicialImages.heightLift f h u))) (pullTransport lambda)) :=
  subcomplex_two_injective _ a ha lambda hA _ (height_image_le_cover Source f h a hh)

/-- Omitting the shift on the 12-face changes an actual lifted triangle. -/
theorem corrupted_face12_height_rejected :
    let A : PreAbstractSimplicialComplex (Fin 3) := ⊤
    let a : Fin 3 → Fin 3 → ℤ := fun u v => (v.val : ℤ) - u.val
    let ha : SimplicialImages.FlatVoltage A a := by intro r u v _; simp only [a]; omega
    let t : Triangle A := ⟨0, 1, 2, by decide, by decide, Finset.insert_nonempty _ _⟩
    edgeEquiv A a ha (face12 (liftTriangle A a ha (t, 0))) ≠ (face12 t, 0) := by
  dsimp only
  intro he
  have hc := congrArg Prod.snd he
  norm_num [edgeEquiv, projectEdge, face12, liftTriangle] at hc

/-- Replacing the original negative transport by +1 changes the ordered cover boundary. -/
theorem corrupted_negative_transport_rejected [CharZero K] :
    let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
    let a : Fin 2 → Fin 2 → ℤ := fun _ _ => 0
    let ha : SimplicialImages.FlatVoltage A a := by intro r u v _; simp [a]
    let e : Edge A := ⟨0, 1, by decide, Finset.insert_nonempty _ _⟩
    vertexChains A a ha (boundaryOne (cover A a) (pullTransport (fun _ _ => (-1 : K)))
      (Finsupp.single (liftEdge A a ha (e, 0)) 1)) ≠
      Finsupp.single ((incidence A).dst e, 0) 1 -
        Finsupp.single ((incidence A).src e, 0) 1 := by
  dsimp only
  intro he
  let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
  let a : Fin 2 → Fin 2 → ℤ := fun _ _ => 0
  have ha : SimplicialImages.FlatVoltage A a := by intro r u v _; simp [a]
  let e : Edge A := ⟨0, 1, by decide, Finset.insert_nonempty _ _⟩
  have hb := LinearMap.congr_fun (boundary_one A a ha (fun _ _ => (-1 : K)))
    (Finsupp.single (liftEdge A a ha (e, 0)) 1)
  change vertexChains A a ha (boundaryOne (cover A a) (pullTransport (fun _ _ => (-1 : K)))
    (Finsupp.single (liftEdge A a ha (e, 0)) 1)) = _ at hb
  rw [hb] at he
  have hc := congrArg (fun c : VoltageChains.LiftChain K (Vertex A) =>
    c (⟨1, Finset.singleton_nonempty _⟩, 0)) he
  norm_num [edgeChains, Finsupp.domLCongr, edgeEquiv, projectEdge,
    VoltageChains.liftedOne, liftEdge, incidence, Finsupp.single_apply, A, a, e] at hc

theorem specialize_boundary_two (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : SimplicialImages.FlatVoltage A a) (lambda : V → V → K)
    (x : Triangle (cover A a) →₀ K) :
    VoltageChains.specialize
      (edgeLaurentChains A a ha (boundaryTwo (cover A a) (pullTransport lambda) x)) =
      boundaryTwo A lambda (VoltageChains.specialize (triangleLaurentChains A a ha x)) := by
  rw [laurent_boundary_two]
  exact LinearMap.congr_fun (VoltageChains.specialize_boundary_two (incidence A)
    (fun e => lambda e.src e.dst) (fun e => a e.src e.dst)) (triangleLaurentChains A a ha x)

end D2RelationGap.OrderedVoltageCover
