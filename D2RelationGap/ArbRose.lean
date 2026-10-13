import D2RelationGap.PresentationRose
import D2RelationGap.GenericFox

/-!
The three-edge rose for an ARBITRARY number `m` of generators, on the vertex type ℕ:
root 0 and, for generator i, the private vertices 2i+1 and 2i+2. A field-unit transport
`q` carries q_i on the closing edge of petal i; it is flat on every face of size at
most two, so no vertex case analysis is needed. Raw signed words over `Fin m` give
literal closed paths of length 3L; their loop classes, holonomy and weighted chains are
the free evaluation, the character and the evaluated left Fox derivative
(`GenericFox.D`). This is the base of the arbitrary-rank presentation compiler used for
the deficiency statement. OpenAI, "A Counterexample to Wall's D(2) Problem"
(October 6, 2026), openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
-/
noncomputable section
namespace D2RelationGap.ArbRose
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops PresentationRose

variable {m : ℕ}

def b (i : Fin m) : ℕ := 2*i.val+1
def c (i : Fin m) : ℕ := 2*i.val+2

def petal (i : Fin m) : Fin 3 → Finset ℕ
  | 0 => {0, b i}
  | 1 => {b i, c i}
  | 2 => {c i, 0}

def rose (m : ℕ) : PreAbstractSimplicialComplex ℕ where
  faces := {s | s.Nonempty ∧ (s ⊆ {0} ∨ ∃ (i : Fin m) (j : Fin 3), s ⊆ petal i j)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    rcases hs.2 with h | ⟨i, j, h⟩
    · exact ⟨ht, Or.inl (hts.trans h)⟩
    · exact ⟨ht, Or.inr ⟨i, j, hts.trans h⟩⟩

theorem petal_face (i : Fin m) (j : Fin 3) : petal i j ∈ rose m := by
  refine ⟨?_, Or.inr ⟨i, j, Finset.Subset.refl _⟩⟩
  fin_cases j <;> exact Finset.insert_nonempty _ _

theorem root_face (m : ℕ) : ({0} : Finset ℕ) ∈ rose m :=
  ⟨Finset.singleton_nonempty _, Or.inl (Finset.Subset.refl _)⟩

theorem petal_card (i : Fin m) (j : Fin 3) : (petal i j).card ≤ 2 := by
  fin_cases j <;> exact Finset.card_le_two

theorem dimension_at_most_one (m : ℕ) (s : Finset ℕ) (hs : s ∈ rose m) : s.card ≤ 2 := by
  rcases hs.2 with h | ⟨i, j, h⟩
  · exact (Finset.card_le_card h).trans (by simp)
  · exact (Finset.card_le_card h).trans (petal_card i j)

instance triangles_empty (m : ℕ) : IsEmpty (Triangle (rose m)) := ⟨fun t => by
  have hh := dimension_at_most_one m (triangleFace t) t.face
  rw [triangleFace_card] at hh
  omega⟩

abbrev root (m : ℕ) : Vertex (rose m) := ⟨0, root_face m⟩

def generatorLoop (i : Fin m) : Path (rose m) 0 0 :=
  .cons (petal_face i 0) (.cons (petal_face i 1) (.cons (petal_face i 2) (.refl 0 (root_face m))))

/-- The petal whose closing vertex is `x`, if any. -/
def closingGen (m : ℕ) (x : ℕ) : Option (Fin m) :=
  if h : 0 < x ∧ x % 2 = 0 ∧ x / 2 - 1 < m then some ⟨x / 2 - 1, h.2.2⟩ else none

theorem closingGen_c (i : Fin m) : closingGen m (c i) = some i := by
  have h : 0 < c i ∧ c i % 2 = 0 ∧ c i / 2 - 1 < m := by
    refine ⟨by simp [c], by simp only [c]; omega, ?_⟩
    have := i.isLt; simp only [c]; omega
  rw [closingGen, dite_eq_left h]
  congr 1
  apply Fin.ext
  simp only [c]; omega

theorem closingGen_zero (m : ℕ) : closingGen m 0 = none := by simp [closingGen]

theorem closingGen_b (i : Fin m) : closingGen m (b i) = none := by
  rw [closingGen, dite_eq_right]
  simp only [b]; omega

variable {K : Type*} [Field K]

def closing (q : Fin m → Kˣ) (x : ℕ) : Kˣ := ((closingGen m x).map q).getD 1

def unit (q : Fin m → Kˣ) (u v : ℕ) : Kˣ :=
  if u = 0 then (closing q v)⁻¹ else if v = 0 then closing q u else 1

theorem unit_self (q : Fin m → Kˣ) (u : ℕ) : unit q u u = 1 := by
  by_cases hu : u = 0
  · subst hu; simp [unit, closing, closingGen_zero m]
  · simp [unit, hu]

theorem unit_swap (q : Fin m → Kˣ) (u v : ℕ) : unit q u v * unit q v u = 1 := by
  by_cases hu : u = 0 <;> by_cases hv : v = 0
  · subst hu; subst hv; simp [unit, closing, closingGen_zero m]
  · simp [unit, hu, hv]
  · simp [unit, hu, hv]
  · simp [unit, hu, hv]

theorem two_equal (u v w : ℕ) (h : ({u, v, w} : Finset ℕ).card ≤ 2) : u = v ∨ v = w ∨ u = w := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  rw [Finset.card_insert_of_notMem (by simp [h1, h3]), Finset.card_pair h2] at h
  omega

theorem unit_flat (q : Fin m → Kˣ) (u v w : ℕ) (ht : ({u, v, w} : Finset ℕ) ∈ rose m) :
    unit q u v * unit q v w = unit q u w := by
  rcases two_equal u v w (dimension_at_most_one m _ ht) with rfl | rfl | rfl
  · rw [unit_self, one_mul]
  · rw [unit_self, mul_one]
  · rw [unit_swap, unit_self]

def transport (q : Fin m → Kˣ) : Transport (K := K) (rose m) := ⟨unit q, unit_flat q⟩

theorem closing_c (q : Fin m → Kˣ) (i : Fin m) : closing q (c i) = q i := by
  simp [closing, closingGen_c]
theorem closing_b (q : Fin m → Kˣ) (i : Fin m) : closing q (b i) = 1 := by
  simp [closing, closingGen_b]

theorem b_ne_zero (i : Fin m) : b i ≠ 0 := by simp [b]
theorem c_ne_zero (i : Fin m) : c i ≠ 0 := by simp [c]

theorem generator_value (q : Fin m → Kˣ) (i : Fin m) :
    value (transport q) (generatorLoop i) = q i := by
  simp [generatorLoop, value, transport, unit, closing_b, closing_c, b_ne_zero, c_ne_zero]

/-! Raw signed words over `Fin m`. -/

abbrev ALetter (m : ℕ) := Fin m × Bool
abbrev AWord (m : ℕ) := List (ALetter m)

def freeLetter (l : ALetter m) : FreeGroup (Fin m) :=
  if l.2 then FreeGroup.of l.1 else (FreeGroup.of l.1)⁻¹
def freeWord (w : AWord m) : FreeGroup (Fin m) := (w.map freeLetter).prod

@[simp] theorem freeWord_nil : freeWord ([] : AWord m) = 1 := rfl
@[simp] theorem freeWord_cons (l : ALetter m) (w : AWord m) :
    freeWord (l :: w) = freeLetter l * freeWord w := rfl

theorem exists_word (f : FreeGroup (Fin m)) : ∃ w : AWord m, freeWord w = f := by
  induction f using FreeGroup.induction_on with
  | one => exact ⟨[], rfl⟩
  | of g => exact ⟨[(g, true)], by simp [freeWord, freeLetter]⟩
  | inv_of g _ => exact ⟨[(g, false)], by simp [freeWord, freeLetter]⟩
  | mul a b ha hb =>
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    exact ⟨u ++ v, by simp [freeWord, List.map_append, List.prod_append]⟩

def letterPath (l : ALetter m) : Path (rose m) 0 0 :=
  if l.2 then generatorLoop l.1 else reverse (generatorLoop l.1)

def wordPath : AWord m → Path (rose m) 0 0
  | [] => .refl 0 (root_face m)
  | l :: w => append (letterPath l) (wordPath w)

instance roseLoopGroup : Group (Loop (rose m) (root m)) := loopGroup (rose m) (root m)

def evalLoops : FreeGroup (Fin m) →* Loop (rose m) (root m) :=
  FreeGroup.lift (fun i => Quotient.mk _ (generatorLoop i))

theorem class_letter (l : ALetter m) :
    (Quotient.mk _ (letterPath l) : Loop (rose m) (root m)) = evalLoops (freeLetter l) := by
  rcases l with ⟨g, h⟩
  cases h
  · change (Quotient.mk _ (reverse (generatorLoop g)) : Loop (rose m) (root m)) =
      evalLoops ((FreeGroup.of g)⁻¹)
    rw [map_inv]
    change (Quotient.mk _ (generatorLoop g) : Loop (rose m) (root m))⁻¹ =
      (FreeGroup.lift _ (FreeGroup.of g))⁻¹
    rw [FreeGroup.lift_apply_of]
  · change (Quotient.mk _ (generatorLoop g) : Loop (rose m) (root m)) =
      FreeGroup.lift _ (FreeGroup.of g)
    rw [FreeGroup.lift_apply_of]

theorem class_word (w : AWord m) :
    (Quotient.mk _ (wordPath w) : Loop (rose m) (root m)) = evalLoops (freeWord w) := by
  induction w with
  | nil => rw [freeWord_nil, map_one]; rfl
  | cons l w ih =>
    calc
      (Quotient.mk _ (wordPath (l :: w)) : Loop (rose m) (root m)) =
          (Quotient.mk _ (letterPath l) : Loop (rose m) (root m)) * Quotient.mk _ (wordPath w) := rfl
      _ = evalLoops (freeLetter l) * evalLoops (freeWord w) :=
        congrArg₂ (fun x y : Loop (rose m) (root m) => x * y) (class_letter l) ih
      _ = evalLoops (freeWord (l :: w)) := by rw [freeWord_cons, map_mul]

/-- Holonomy of the literal free evaluation is the character itself. -/
theorem character_agreement (χ : FreeGroup (Fin m) →* K) :
    (holonomy (transport (fun i => GenericFox.unitsChar χ (FreeGroup.of i))) (root m)).comp evalLoops =
      GenericFox.unitsChar χ := by
  apply FreeGroup.ext_hom
  intro g
  change value (transport _) (generatorLoop g) = _
  exact generator_value _ g

theorem path_value (χ : FreeGroup (Fin m) →* K) {p : Path (rose m) 0 0} (f : FreeGroup (Fin m))
    (hp : (Quotient.mk _ p : Loop (rose m) (root m)) = evalLoops f) :
    (value (transport (fun i => GenericFox.unitsChar χ (FreeGroup.of i))) p : K) = χ f := by
  have hh := DFunLike.congr_fun (character_agreement χ) f
  change holonomy _ (root m) (evalLoops f) = _ at hh
  rw [← hp] at hh
  exact congrArg (fun z : Kˣ => (z : K)) hh

theorem word_value (χ : FreeGroup (Fin m) →* K) (w : AWord m) :
    (value (transport (fun i => GenericFox.unitsChar χ (FreeGroup.of i))) (wordPath w) : K) =
      χ (freeWord w) :=
  path_value χ _ (class_word w)

/-! Lengths and noncollapsed edges. -/

theorem generator_noncollapsed (i : Fin m) : Noncollapsed (generatorLoop i) := by
  refine ⟨(b_ne_zero i).symm, ?_, c_ne_zero i, True.intro⟩
  simp [b, c]

theorem letter_noncollapsed (l : ALetter m) : Noncollapsed (letterPath l) := by
  rcases l with ⟨g, h⟩
  cases h
  · exact noncollapsed_reverse _ (generator_noncollapsed g)
  · exact generator_noncollapsed g

theorem word_noncollapsed (w : AWord m) : Noncollapsed (wordPath w) := by
  induction w with
  | nil => trivial
  | cons l w ih => exact noncollapsed_append _ _ (letter_noncollapsed l) ih

theorem letter_length (l : ALetter m) : PolygonSource.length (letterPath l) = 3 := by
  rcases l with ⟨g, h⟩
  cases h
  · rw [letterPath]; simp only [Bool.false_eq_true, ite_false, length_reverse]; rfl
  · rw [letterPath]; simp only [ite_true]; rfl

theorem word_length (w : AWord m) : PolygonSource.length (wordPath w) = 3*w.length := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [wordPath, length_append, letter_length, ih, List.length_cons]; omega

/-! Weighted chains: the evaluated left Fox derivative. -/

def firstEdge (i : Fin m) : Edge (rose m) := ⟨0, b i, by simp [b], petal_face i 0⟩

def generatorChain (q : Fin m → Kˣ) (i : Fin m) : Edge (rose m) →₀ K :=
  PathChains.chain (transport q) (generatorLoop i)

theorem generatorChain_first (q : Fin m → Kˣ) (i j : Fin m) :
    generatorChain q i (firstEdge j) = if i = j then 1 else 0 := by
  have hb : b i = b j ↔ i = j := by
    constructor
    · intro h; apply Fin.ext; simp only [b] at h; omega
    · rintro rfl; rfl
  have hbc : c i ≠ b j := fun h => by simp only [b, c] at h; omega
  have hb0 : b i ≠ 0 := b_ne_zero i
  have hlt0b : (0 : ℕ) < b i := by simp [b]
  have hltbc : b i < c i := by simp [b, c]
  have hlt0c : (0 : ℕ) < c i := by simp [c]
  have e1 : edge (transport q) 0 (b i) (petal_face i 0) =
      Finsupp.single ⟨0, b i, hlt0b, petal_face i 0⟩ 1 := by simp [edge, hlt0b]
  have e2 : edge (transport q) (b i) (c i) (petal_face i 1) =
      Finsupp.single ⟨b i, c i, hltbc, petal_face i 1⟩ 1 := by simp [edge, hltbc]
  have h2 : ({0, c i} : Finset ℕ) ∈ rose m := by
    have := petal_face (m := m) i 2
    rwa [show petal i 2 = {c i, 0} from rfl, Finset.pair_comm] at this
  have e3 : edge (transport q) (c i) 0 (petal_face i 2) =
      -(coeff (transport q) (c i) 0 • Finsupp.single ⟨0, c i, hlt0c, h2⟩ 1) := by
    simp [edge, hlt0c]
  have n2 : firstEdge j ≠ (⟨b i, c i, hltbc, petal_face i 1⟩ : Edge (rose m)) :=
    fun h => hb0 (congrArg Edge.src h).symm
  have n3 : firstEdge j ≠ (⟨0, c i, hlt0c, h2⟩ : Edge (rose m)) :=
    fun h => hbc (congrArg Edge.dst h).symm
  simp only [generatorChain, PathChains.chain, generatorLoop]
  rw [e1, e2, e3]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.neg_apply,
    Finsupp.single_eq_of_ne n2, Finsupp.single_eq_of_ne n3, smul_eq_mul, Finsupp.coe_zero,
    Pi.zero_apply, mul_zero, neg_zero, add_zero]
  by_cases h : i = j
  · subst h; exact Finsupp.single_eq_same.trans (ite_eq_left rfl).symm
  · rw [ite_eq_right h]
    apply Finsupp.single_eq_of_ne
    intro he
    exact h ((hb).mp (congrArg Edge.dst he).symm)

def roseMap (q : Fin m → Kˣ) : (Fin m → K) →ₗ[K] (Edge (rose m) →₀ K) where
  toFun x := ∑ g, x g • generatorChain q g
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z x := by simp [Finset.smul_sum, smul_smul]

theorem roseMap_first (q : Fin m → Kˣ) (x : Fin m → K) (h : Fin m) :
    roseMap q x (firstEdge h) = x h := by
  simp [roseMap, generatorChain_first]

theorem roseMap_injective (q : Fin m → Kˣ) : Function.Injective (roseMap q) := by
  intro x y he
  funext g
  exact (roseMap_first q x g).symm.trans
    ((congrArg (fun z : Edge (rose m) →₀ K => z (firstEdge g)) he).trans (roseMap_first q y g))

theorem roseMap_single (q : Fin m → Kˣ) (g : Fin m) :
    roseMap q (Pi.single g 1) = generatorChain q g := by
  simp [roseMap, Pi.single_apply]

theorem word_chain (χ : FreeGroup (Fin m) →* K) (w : AWord m) :
    PathChains.chain (transport (fun i => GenericFox.unitsChar χ (FreeGroup.of i))) (wordPath w) =
      roseMap (fun i => GenericFox.unitsChar χ (FreeGroup.of i)) (GenericFox.D χ (freeWord w)) := by
  set q := fun i => GenericFox.unitsChar χ (FreeGroup.of i)
  induction w with
  | nil => simp [wordPath, PathChains.chain]
  | cons l w ih =>
    have hletter : PathChains.chain (transport q) (letterPath l) =
        roseMap q (GenericFox.D χ (freeLetter l)) := by
      rcases l with ⟨g, h⟩
      cases h
      · change PathChains.chain (transport q) (reverse (generatorLoop g)) =
          roseMap q (GenericFox.D χ (FreeGroup.of g)⁻¹)
        rw [StellarSubdivision.chain_reverse, generator_value, GenericFox.D_inv, map_neg, map_smul,
          GenericFox.D_of, roseMap_single]
        have hh : χ ((FreeGroup.of g)⁻¹) = ((q g)⁻¹ : Kˣ) := by
          simp [q, GenericFox.unitsChar_val, map_inv]
        rw [hh]
        rfl
      · change generatorChain q g = roseMap q (GenericFox.D χ (FreeGroup.of g))
        rw [GenericFox.D_of, roseMap_single]
    have hv : (value (transport q) (letterPath l) : K) = χ (freeLetter l) :=
      path_value χ _ (class_letter l)
    rw [wordPath, PathChains.chain_append, hletter, ih, hv, freeWord_cons, GenericFox.D_mul,
      map_add, map_smul]

end D2RelationGap.ArbRose
