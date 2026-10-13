import D2RelationGap.LaurentPersistence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
An explicit two-dimensional incidence cover and its finite-support chains.
OpenAI's "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, Section 2,
supplies the tower argument. Realization, simplicial maps and presentation-complex
adapters remain open; no topological torsion obstruction is asserted here.
-/

noncomputable section
namespace D2RelationGap.VoltageChains

/-- The face identities of a two-truncated semisimplicial set. No assumption
of vanishing homology, vertex growth or existence of voltage is built in. -/
structure TwoComplex (V E T : Type*) where
  src : E → V
  dst : E → V
  edge01 : T → E
  edge02 : T → E
  edge12 : T → E
  first : ∀ t, src (edge01 t) = src (edge02 t)
  middle : ∀ t, dst (edge01 t) = src (edge12 t)
  last : ∀ t, dst (edge12 t) = dst (edge02 t)

variable {V E T K : Type*} [Field K]

/-- The actual lifted incidence data. Full covers may be disconnected. -/
def lift (A : TwoComplex V E T) (a : E → ℤ)
    (ha : ∀ t, a (A.edge01 t) + a (A.edge12 t) = a (A.edge02 t)) :
    TwoComplex (V × ℤ) (E × ℤ) (T × ℤ) where
  src en := (A.src en.1, en.2)
  dst en := (A.dst en.1, en.2 + a en.1)
  edge01 tn := (A.edge01 tn.1, tn.2)
  edge02 tn := (A.edge02 tn.1, tn.2)
  edge12 tn := (A.edge12 tn.1, tn.2 + a (A.edge01 tn.1))
  first tn := by simp [A.first]
  middle tn := by simp [A.middle]
  last tn := by simp [A.last, add_assoc, ha]

abbrev LiftChain (K : Type*) [Field K] (S : Type*) := (S × ℤ) →₀ K
abbrev OrbitChain (K : Type*) [Field K] (S : Type*) := S →₀ LaurentPolynomial K

/-- Regroup every finite-support chain by base cell and integer height.
This is an equivalence, rather than an unrestricted product of fibers. -/
def orbitEquiv (S : Type*) : LiftChain K S ≃ₗ[K] OrbitChain K S :=
  (Finsupp.curryLinearEquiv K (α := S) (β := ℤ) (M := K)).trans
    (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv K).symm)

theorem orbitEquiv_single {S : Type*} (s : S) (n : ℤ) (c : K) :
    orbitEquiv S (Finsupp.single (s, n) c) =
      Finsupp.single s (LaurentPolynomial.C c * LaurentPolynomial.T n) := by
  change Finsupp.mapRange (AddMonoidAlgebra.coeffLinearEquiv K).symm (map_zero _)
    (Finsupp.curry (Finsupp.single (s, n) c)) = _
  rw [Finsupp.curry_single, Finsupp.mapRange_single]
  congr 1
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rfl

/-- Canonical deck translation moves cell heights and leaves coefficients intact. -/
def deck {S : Type*} (k : ℤ) : LiftChain K S →ₗ[K] LiftChain K S :=
  Finsupp.lmapDomain K K (fun sn => (sn.1, sn.2 + k))

theorem deck_zero {S : Type*} : (deck 0 : LiftChain K S →ₗ[K] LiftChain K S) =
    LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨s, n⟩ c
  simp [deck, Finsupp.lmapDomain_apply]

theorem deck_add {S : Type*} (k l : ℤ) :
    (deck (k + l) : LiftChain K S →ₗ[K] LiftChain K S) = (deck l).comp (deck k) := by
  apply Finsupp.lhom_ext
  rintro ⟨s, n⟩ c
  simp [deck, Finsupp.lmapDomain_apply, add_assoc]

theorem deck_inverse {S : Type*} (k : ℤ) :
    (deck (-k) : LiftChain K S →ₗ[K] LiftChain K S).comp (deck k) = LinearMap.id := by
  rw [← deck_add, add_neg_cancel, deck_zero]

def orbitMultiply {S : Type*} (p : LaurentPolynomial K) :
    OrbitChain K S →ₗ[K] OrbitChain K S where
  toFun c := p • c
  map_add' := smul_add p
  map_smul' r c := smul_comm p r c

theorem orbit_deck {S : Type*} (k : ℤ) :
    (orbitEquiv S).toLinearMap.comp (deck k) =
      (orbitMultiply (K := K) (LaurentPolynomial.T k)).comp (orbitEquiv S).toLinearMap := by
  apply Finsupp.lhom_ext
  rintro ⟨s, n⟩ c
  change orbitEquiv S (deck k (Finsupp.single (s, n) c)) =
    (LaurentPolynomial.T k : LaurentPolynomial K) • orbitEquiv S (Finsupp.single (s, n) c)
  simp only [deck, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    orbitEquiv_single, Finsupp.smul_single, smul_eq_mul]
  congr 1
  rw [← mul_assoc, mul_comm (LaurentPolynomial.T k), mul_assoc,
    ← LaurentPolynomial.T_add]
  simp [add_comm]

/-- Boundary of a lifted edge with its original first-vertex coefficient fiber. -/
def liftedOne (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    LiftChain K E →ₗ[K] LiftChain K V :=
  Finsupp.linearCombination K fun en =>
    lambda en.1 • Finsupp.single (A.dst en.1, en.2 + a en.1) 1 -
      Finsupp.single (A.src en.1, en.2) 1

/-- The first face starts at height n+a01; its coefficient is lambda01. -/
def liftedTwo (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    LiftChain K T →ₗ[K] LiftChain K E :=
  Finsupp.linearCombination K fun tn =>
    lambda (A.edge01 tn.1) •
      Finsupp.single (A.edge12 tn.1, tn.2 + a (A.edge01 tn.1)) 1 -
      Finsupp.single (A.edge02 tn.1, tn.2) 1 +
      Finsupp.single (A.edge01 tn.1, tn.2) 1

theorem deck_boundary_one (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ)
    (k : ℤ) : (liftedOne A lambda a).comp (deck k) =
      (deck k).comp (liftedOne A lambda a) := by
  apply Finsupp.lhom_ext
  rintro ⟨e, n⟩ c
  simp [liftedOne, deck, Finsupp.lmapDomain_apply, Finsupp.linearCombination_single,
    Finsupp.mapDomain_sub, add_comm, add_left_comm]

theorem deck_boundary_two (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ)
    (k : ℤ) : (liftedTwo A lambda a).comp (deck k) =
      (deck k).comp (liftedTwo A lambda a) := by
  apply Finsupp.lhom_ext
  rintro ⟨t, n⟩ c
  simp [liftedTwo, deck, Finsupp.lmapDomain_apply, Finsupp.linearCombination_single,
    Finsupp.mapDomain_sub, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    add_assoc, add_comm]

/-- Laurent boundary on the chosen height-zero edge representatives. -/
def laurentOne (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    OrbitChain K E →ₗ[LaurentPolynomial K] OrbitChain K V :=
  Finsupp.linearCombination (LaurentPolynomial K) fun e =>
    LaurentPersistence.transport (lambda e) (a e) • Finsupp.single (A.dst e) 1 -
      Finsupp.single (A.src e) 1

def laurentTwo (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    OrbitChain K T →ₗ[LaurentPolynomial K] OrbitChain K E :=
  Finsupp.linearCombination (LaurentPolynomial K) fun t =>
    LaurentPersistence.transport (lambda (A.edge01 t)) (a (A.edge01 t)) •
      Finsupp.single (A.edge12 t) 1 - Finsupp.single (A.edge02 t) 1 +
      Finsupp.single (A.edge01 t) 1

theorem lifted_boundary_chain (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ)
    (hl : ∀ t, lambda (A.edge01 t) * lambda (A.edge12 t) = lambda (A.edge02 t))
    (ha : ∀ t, a (A.edge01 t) + a (A.edge12 t) = a (A.edge02 t)) :
    (liftedOne A lambda a).comp (liftedTwo A lambda a) = 0 := by
  ext tn
  rcases tn with ⟨t, n⟩
  simp [liftedOne, liftedTwo, Finsupp.linearCombination_single, A.first, A.middle,
    A.last, hl, add_assoc, ha, smul_sub]

theorem orbit_boundary_one (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    (orbitEquiv V).toLinearMap.comp (liftedOne A lambda a) =
      ((laurentOne A lambda a).restrictScalars K).comp (orbitEquiv E).toLinearMap := by
  apply Finsupp.lhom_ext
  intro en c
  rcases en with ⟨e, n⟩
  simp [liftedOne, laurentOne, orbitEquiv_single, Finsupp.linearCombination_single,
    LaurentPersistence.transport, Finsupp.smul_single, smul_eq_mul, smul_sub,
    mul_comm, mul_left_comm, -LaurentPolynomial.T_mul]
  conv_rhs => rw [← mul_assoc, ← LaurentPolynomial.T_add]

theorem orbit_boundary_two (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    (orbitEquiv E).toLinearMap.comp (liftedTwo A lambda a) =
      ((laurentTwo A lambda a).restrictScalars K).comp (orbitEquiv T).toLinearMap := by
  apply Finsupp.lhom_ext
  intro tn c
  rcases tn with ⟨t, n⟩
  simp [liftedTwo, laurentTwo, orbitEquiv_single, Finsupp.linearCombination_single,
    LaurentPersistence.transport, Finsupp.smul_single, smul_eq_mul, smul_sub,
    mul_comm, mul_left_comm, -LaurentPolynomial.T_mul]
  conv_rhs => rw [← mul_assoc, ← LaurentPolynomial.T_add]

def atOneLinear : LaurentPolynomial K →ₗ[K] K where
  toFun := LaurentPersistence.atOne
  map_add' := map_add _
  map_smul' r p := by
    rw [LaurentPolynomial.smul_eq_C_mul, map_mul]
    simp [LaurentPersistence.atOne]

def specialize {S : Type*} : OrbitChain K S →ₗ[K] S →₀ K :=
  Finsupp.mapRange.linearMap atOneLinear

theorem specialize_single {S : Type*} (s : S) (p : LaurentPolynomial K) :
    specialize (Finsupp.single s p) = Finsupp.single s (LaurentPersistence.atOne p) := by
  change Finsupp.mapRange (atOneLinear (K := K)) (map_zero _)
    (Finsupp.single s p) = _
  rw [Finsupp.mapRange_single]
  rfl

theorem specialize_smul {S : Type*} (p : LaurentPolynomial K) (c : OrbitChain K S) :
    specialize (p • c) = LaurentPersistence.atOne p • specialize c := by
  ext s
  change LaurentPersistence.atOne (p * c s) =
    LaurentPersistence.atOne p * LaurentPersistence.atOne (c s)
  exact map_mul _ _ _

/-- Forgetting height is precisely Laurent specialization at one; coefficients
are summed over heights, never changed by the original holonomy. -/
theorem specialize_orbit {S : Type*} :
    (specialize (K := K) (S := S)).comp (orbitEquiv S).toLinearMap =
      Finsupp.lmapDomain K K Prod.fst := by
  apply Finsupp.lhom_ext
  rintro ⟨s, n⟩ c
  simp [orbitEquiv_single, specialize_single, Finsupp.lmapDomain_apply,
    LaurentPersistence.atOne, LaurentPolynomial.eval₂_C_mul_T]

def baseOne (A : TwoComplex V E T) (lambda : E → K) : (E →₀ K) →ₗ[K] V →₀ K :=
  Finsupp.linearCombination K fun e =>
    lambda e • Finsupp.single (A.dst e) 1 - Finsupp.single (A.src e) 1

def baseTwo (A : TwoComplex V E T) (lambda : E → K) : (T →₀ K) →ₗ[K] E →₀ K :=
  Finsupp.linearCombination K fun t =>
    lambda (A.edge01 t) • Finsupp.single (A.edge12 t) 1 -
      Finsupp.single (A.edge02 t) 1 + Finsupp.single (A.edge01 t) 1

theorem liftedOne_eq_boundary_of_lift (A : TwoComplex V E T) (lambda : E → K)
    (a : E → ℤ) (ha : ∀ t, a (A.edge01 t) + a (A.edge12 t) = a (A.edge02 t)) :
    liftedOne A lambda a = baseOne (lift A a ha) (fun en => lambda en.1) := rfl

theorem liftedTwo_eq_boundary_of_lift (A : TwoComplex V E T) (lambda : E → K)
    (a : E → ℤ) (ha : ∀ t, a (A.edge01 t) + a (A.edge12 t) = a (A.edge02 t)) :
    liftedTwo A lambda a = baseTwo (lift A a ha) (fun en => lambda en.1) := rfl

theorem specialize_boundary_one (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    (specialize (K := K)).comp ((laurentOne A lambda a).restrictScalars K) =
      (baseOne A lambda).comp specialize := by
  apply Finsupp.lhom_ext
  intro e p
  simp [laurentOne, baseOne, Finsupp.linearCombination_single, specialize_smul,
    specialize_single, LaurentPersistence.atOne_transport]

theorem specialize_boundary_two (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ) :
    (specialize (K := K)).comp ((laurentTwo A lambda a).restrictScalars K) =
      (baseTwo A lambda).comp specialize := by
  apply Finsupp.lhom_ext
  intro t p
  simp [laurentTwo, baseTwo, Finsupp.linearCombination_single, specialize_smul,
    specialize_single, LaurentPersistence.atOne_transport]

section Coordinates
variable {R I J : Type*} [CommRing R] [Fintype I]

theorem linearCombination_coordinates (v : I → J →₀ R) (c : I →₀ R) :
    (Matrix.of fun j i => v i j).mulVecLin (fun i => c i) =
      fun j => Finsupp.linearCombination R v c j := by
  rw [← Finsupp.linearEquivFunOnFinite_symm_coe R R I c,
    Finsupp.linearCombination_eq_fintype_linearCombination_apply]
  funext j
  simp [Matrix.mulVec, dotProduct, Fintype.linearCombination_apply, mul_comm]

theorem linearCombination_injective_of_specialized [IsDomain R] [Fintype J]
    (phi : R →+* K) (v : I → J →₀ R) (w : I → J →₀ K)
    (hv : ∀ i j, phi (v i j) = w i j)
    (hw : Function.Injective (Finsupp.linearCombination K w)) :
    Function.Injective (Finsupp.linearCombination R v) := by
  let MR : Matrix J I R := Matrix.of fun j i => v i j
  let MK : Matrix J I K := Matrix.of fun j i => w i j
  have hmap : MR.map phi = MK := by
    ext j i
    exact hv i j
  have hK : Function.Injective MK.mulVecLin := by
    intro x y hxy
    let e := Finsupp.linearEquivFunOnFinite K K I
    have hh : Finsupp.linearCombination K w (e.symm x) =
        Finsupp.linearCombination K w (e.symm y) := by
      apply DFunLike.coe_injective
      simpa only [MK, e, ← linearCombination_coordinates,
        Finsupp.linearEquivFunOnFinite_symm_apply] using hxy
    exact e.symm.injective (hw hh)
  have hR : Function.Injective MR.mulVecLin :=
    MatrixPersistence.injective_of_specialized_injective phi MR (hmap.symm ▸ hK)
  intro x y hxy
  apply DFunLike.coe_injective
  apply hR
  simpa only [MR, linearCombination_coordinates] using
    congrArg (fun c : J →₀ R => (fun j => c j)) hxy
end Coordinates

/-- Persistence for the explicit finite-base incidence cover. This is ordinary
finite-support chain injectivity, with no claim yet about topological H2. -/
theorem lifted_two_injective_of_base_two_injective [Fintype E] [Fintype T]
    (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ)
    (h : Function.Injective (baseTwo A lambda)) :
    Function.Injective (liftedTwo A lambda a) := by
  have hL : Function.Injective (laurentTwo A lambda a) := by
    apply linearCombination_injective_of_specialized LaurentPersistence.atOne _ _ _ h
    intro t e
    have hs := LinearMap.congr_fun (specialize_boundary_two A lambda a)
      (Finsupp.single t 1)
    have hs' : specialize (Finsupp.linearCombination (LaurentPolynomial K)
        (fun t => LaurentPersistence.transport (lambda (A.edge01 t)) (a (A.edge01 t)) •
          Finsupp.single (A.edge12 t) 1 - Finsupp.single (A.edge02 t) 1 +
          Finsupp.single (A.edge01 t) 1) (Finsupp.single t 1)) =
        baseTwo A lambda (specialize (Finsupp.single t 1)) := hs
    simp only [Finsupp.linearCombination_single, one_smul, specialize_single,
      map_one] at hs'
    change LaurentPersistence.atOne _ = _
    have hc := congrArg (fun f : E →₀ K => f e) hs'
    change LaurentPersistence.atOne _ = (baseTwo A lambda (Finsupp.single t 1)) e at hc
    simpa only [baseTwo, Finsupp.linearCombination_single, one_smul] using hc
  intro x y hxy
  apply (orbitEquiv T).injective
  apply hL
  have hx := LinearMap.congr_fun (orbit_boundary_two A lambda a) x
  have hy := LinearMap.congr_fun (orbit_boundary_two A lambda a) y
  exact hx.symm.trans ((congrArg (orbitEquiv E) hxy).trans hy)

/-- One ordinary ordered triangle, with edges 01,02,12 numbered 0,1,2. -/
def triangle : TwoComplex (Fin 3) (Fin 3) Unit where
  src e := if e = 2 then 1 else 0
  dst e := if e = 0 then 1 else 2
  edge01 _ := 0
  edge02 _ := 1
  edge12 _ := 2
  first := by decide
  middle := by decide
  last := by decide

theorem corrupted_triangle_voltage_rejected :
    (liftedOne triangle (fun _ => (1 : K)) (fun _ => 1)).comp
      (liftedTwo triangle (fun _ => (1 : K)) (fun _ => 1)) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LiftChain K (Fin 3) => f (2, 2))
    (LinearMap.congr_fun h (Finsupp.single ((), 0) 1))
  norm_num [liftedOne, liftedTwo, triangle, Finsupp.linearCombination_single,
    Finsupp.single_apply] at hc

theorem corrupted_triangle_transport_rejected [CharZero K] :
    let lambda : Fin 3 → K := fun e => if e = 0 then -1 else 1
    (liftedOne triangle lambda (fun _ => 0)).comp
      (liftedTwo triangle lambda (fun _ => 0)) ≠ 0 := by
  dsimp only
  intro h
  have hc := congrArg (fun f : LiftChain K (Fin 3) => f (2, 0))
    (LinearMap.congr_fun h (Finsupp.single ((), 0) 1))
  norm_num [liftedOne, liftedTwo, triangle, Finsupp.linearCombination_single,
    Finsupp.single_apply] at hc

/-- A literal collection of cells closed under every face, without any
homology or injectivity assumption. -/
structure Subcomplex (A : TwoComplex V E T) where
  vertices : Set V
  edges : Set E
  triangles : Set T
  src_mem : ∀ e ∈ edges, A.src e ∈ vertices
  dst_mem : ∀ e ∈ edges, A.dst e ∈ vertices
  edge01_mem : ∀ t ∈ triangles, A.edge01 t ∈ edges
  edge02_mem : ∀ t ∈ triangles, A.edge02 t ∈ edges
  edge12_mem : ∀ t ∈ triangles, A.edge12 t ∈ edges

def Subcomplex.toComplex {A : TwoComplex V E T} (B : Subcomplex A) :
    TwoComplex B.vertices B.edges B.triangles where
  src e := ⟨A.src e.val, B.src_mem e.val e.property⟩
  dst e := ⟨A.dst e.val, B.dst_mem e.val e.property⟩
  edge01 t := ⟨A.edge01 t.val, B.edge01_mem t.val t.property⟩
  edge02 t := ⟨A.edge02 t.val, B.edge02_mem t.val t.property⟩
  edge12 t := ⟨A.edge12 t.val, B.edge12_mem t.val t.property⟩
  first t := Subtype.ext (A.first t.val)
  middle t := Subtype.ext (A.middle t.val)
  last t := Subtype.ext (A.last t.val)

/-- Extension by zero along a subtype. All chains have finite support. -/
def extend {S : Type*} (s : Set S) : (s →₀ K) →ₗ[K] S →₀ K :=
  Finsupp.lmapDomain K K Subtype.val

theorem extend_injective {S : Type*} (s : Set S) :
    Function.Injective (extend (K := K) s) :=
  Finsupp.mapDomain_injective Subtype.val_injective

theorem subcomplex_boundary_one {A : TwoComplex V E T} (B : Subcomplex A)
    (lambda : E → K) :
    (extend B.vertices).comp (baseOne B.toComplex (fun e => lambda e.val)) =
      (baseOne A lambda).comp (extend B.edges) := by
  apply Finsupp.lhom_ext
  intro e c
  simp [baseOne, extend, Finsupp.lmapDomain_apply, Finsupp.linearCombination_single,
    Finsupp.mapDomain_sub, Subcomplex.toComplex]

theorem subcomplex_boundary_two {A : TwoComplex V E T} (B : Subcomplex A)
    (lambda : E → K) :
    (extend B.edges).comp (baseTwo B.toComplex (fun e => lambda e.val)) =
      (baseTwo A lambda).comp (extend B.triangles) := by
  apply Finsupp.lhom_ext
  intro t c
  simp [baseTwo, extend, Finsupp.lmapDomain_apply, Finsupp.linearCombination_single,
    Finsupp.mapDomain_sub, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    Subcomplex.toComplex]

/-- Restriction to a closed subcomplex preserves degree-two injectivity.
No assertion about fundamental-group inclusions is needed. -/
theorem subcomplex_two_injective {A : TwoComplex V E T} (B : Subcomplex A)
    (lambda : E → K) (h : Function.Injective (baseTwo A lambda)) :
    Function.Injective (baseTwo B.toComplex (fun e => lambda e.val)) := by
  intro x y hxy
  apply extend_injective B.triangles
  apply h
  have hx := LinearMap.congr_fun (subcomplex_boundary_two B lambda) x
  have hy := LinearMap.congr_fun (subcomplex_boundary_two B lambda) y
  exact hx.symm.trans ((congrArg (extend B.edges) hxy).trans hy)

theorem lifted_subcomplex_two_injective [Fintype E] [Fintype T]
    (A : TwoComplex V E T) (lambda : E → K) (a : E → ℤ)
    (ha : ∀ t, a (A.edge01 t) + a (A.edge12 t) = a (A.edge02 t))
    (B : Subcomplex (lift A a ha)) (h : Function.Injective (baseTwo A lambda)) :
    Function.Injective (baseTwo B.toComplex (fun e => lambda e.val.1)) := by
  apply subcomplex_two_injective B (fun en => lambda en.1)
  rw [← liftedTwo_eq_boundary_of_lift A lambda a ha]
  exact lifted_two_injective_of_base_two_injective A lambda a h

/-- A triangle cannot be retained while deleting its faces. -/
theorem missing_triangle_faces_rejected :
    ¬ ∃ B : Subcomplex triangle, B.triangles = Set.univ ∧ B.edges = ∅ := by
  rintro ⟨B, ht, he⟩
  have hm := B.edge01_mem () (by rw [ht]; trivial)
  rw [he] at hm
  exact hm

end D2RelationGap.VoltageChains
