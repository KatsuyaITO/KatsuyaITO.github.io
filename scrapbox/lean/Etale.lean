/-
  Lean 4 でエタール・コホモロジーをセルフコンテインドに定義する。
  Mathlib を import しない。Lean 4 のコア（Type, Prop, Nat, Int, Fin, List, Quot）だけを使う。
-/
namespace Tutorial

-- §§ ring
/-- 可換環。台となる型 `R` に、足し算・掛け算・マイナス・0・1 と、8つの公理を載せたもの。 -/
class CommRing (R : Type) extends Add R, Mul R, Neg R, Zero R, One R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm  : ∀ a b : R, a + b = b + a
  zero_add  : ∀ a : R, 0 + a = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm  : ∀ a b : R, a * b = b * a
  one_mul   : ∀ a : R, 1 * a = a
  mul_add   : ∀ a b c : R, a * (b + c) = a * b + a * c

-- §§ ring_int
/-- 整数 `ℤ` は可換環である。公理はすべて Lean コアの補題で埋まる。 -/
instance : CommRing Int where
  add_assoc := Int.add_assoc
  add_comm  := Int.add_comm
  zero_add  := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  mul_comm  := Int.mul_comm
  one_mul   := Int.one_mul
  mul_add   := Int.mul_add

example : (2 : Int) * 3 + -6 = 0 := rfl
example (R : Type) [CommRing R] (a : R) : a * 1 = 1 * a := CommRing.mul_comm a 1

-- §§ ring_lemmas
section RingLemmas
variable {R : Type} [CommRing R]
open CommRing

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]
theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]
theorem mul_one (a : R) : a * 1 = a := by rw [mul_comm, one_mul]
theorem add_mul (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h' : -a + (a + b) = -a + (a + c) := congrArg (fun x => -a + x) h
  rwa [← add_assoc, ← add_assoc, neg_add_cancel, zero_add, zero_add] at h'

theorem mul_zero (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← mul_add, zero_add, add_zero]
theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [h, add_neg_cancel]
theorem mul_neg (a b : R) : a * -b = -(a * b) := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← mul_add, add_neg_cancel, mul_zero]
theorem neg_add (a b : R) : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  -- ゴール: (a + b) + (-a + -b) = 0
  rw [add_assoc, add_comm b, add_assoc, neg_add_cancel, add_zero, add_neg_cancel]
end RingLemmas

-- §§ hom
/-- 環準同型。写像であって、足し算・掛け算・1 を保つもの。 -/
structure RingHom (R S : Type) [CommRing R] [CommRing S] where
  toFun   : R → S
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_one : toFun 1 = 1

infixr:25 " →ᵣ " => RingHom

instance {R S : Type} [CommRing R] [CommRing S] : CoeFun (R →ᵣ S) (fun _ => R → S) :=
  ⟨RingHom.toFun⟩

section HomLemmas
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem RingHom.map_zero (f : R →ᵣ S) : f 0 = 0 := by
  apply add_left_cancel (a := f 0)
  rw [← f.map_add, CommRing.zero_add, add_zero]

theorem RingHom.map_neg (f : R →ᵣ S) (a : R) : f (-a) = -(f a) := by
  symm; apply neg_eq_of_add_eq_zero
  rw [← f.map_add, add_neg_cancel, f.map_zero]

/-- 恒等写像は環準同型。 -/
def RingHom.id (R : Type) [CommRing R] : R →ᵣ R :=
  ⟨fun a => a, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- 環準同型の合成。 -/
def RingHom.comp (g : S →ᵣ T) (f : R →ᵣ S) : R →ᵣ T where
  toFun a := g (f a)
  map_add a b := by rw [f.map_add, g.map_add]
  map_mul a b := by rw [f.map_mul, g.map_mul]
  map_one := by rw [f.map_one, g.map_one]

/-- 環準同型の相等は写像の相等で決まる。 -/
theorem RingHom.ext {f g : R →ᵣ S} (h : ∀ a, f a = g a) : f = g := by
  cases f; cases g
  have : _ = _ := funext h
  simp only at this
  subst this
  rfl
end HomLemmas

-- §§ ideal
section Ideals
variable {R : Type} [CommRing R]

/-- イデアル。0 を含み、足し算で閉じ、環の元を掛けても閉じている部分集合。 -/
structure Ideal (R : Type) [CommRing R] where
  carrier  : R → Prop
  zero_mem : carrier 0
  add_mem  : ∀ {a b}, carrier a → carrier b → carrier (a + b)
  mul_mem  : ∀ (r : R) {a}, carrier a → carrier (r * a)

instance : Membership R (Ideal R) := ⟨fun I a => I.carrier a⟩

-- §§ ideal_prime
/-- 素イデアル。全体ではなく、`ab ∈ P` なら `a ∈ P` か `b ∈ P`。 -/
def Ideal.IsPrime (P : Ideal R) : Prop :=
  (1 : R) ∉ P ∧ ∀ {a b : R}, a * b ∈ P → a ∈ P ∨ b ∈ P

/-- 可逆元（単元）。 -/
def IsUnit (a : R) : Prop := ∃ b, a * b = 1

/-- 局所環。`0 ≠ 1` で、任意の `a` について `a` か `1 - a` が可逆。
（「非可逆元全体がイデアルになる」「極大イデアルがただ一つ」と同値。） -/
def IsLocalRing (R : Type) [CommRing R] : Prop :=
  (0 : R) ≠ 1 ∧ ∀ a : R, IsUnit a ∨ IsUnit (1 + -a)

/-- 局所準同型。非可逆元を非可逆元へ送る（同じことだが、`φ a` が可逆なら `a` も可逆）。 -/
def RingHom.IsLocal {S : Type} [CommRing S] (φ : R →ᵣ S) : Prop :=
  ∀ a : R, IsUnit (φ a) → IsUnit a

-- §§ ideal_ker
/-- 環準同型の核 `ker f = {a | f a = 0}` はイデアル。 -/
def RingHom.ker {S : Type} [CommRing S] (f : R →ᵣ S) : Ideal R where
  carrier a := f a = 0
  zero_mem := f.map_zero
  add_mem {a b} ha hb := by
    show f (a + b) = 0
    rw [f.map_add, ha, hb, add_zero]
  mul_mem r {a} ha := by
    show f (r * a) = 0
    rw [f.map_mul, ha, mul_zero]

/-- 有限個の元 `l = [x₁, …, xₙ]` が生成するイデアルの元、すなわち有限和 `Σ rᵢ xᵢ`。 -/
inductive InSpan (l : List R) : R → Prop
  | zero : InSpan l 0
  | add {a b} : InSpan l a → InSpan l b → InSpan l (a + b)
  | smul (r : R) {x} : x ∈ l → InSpan l (r * x)

/-- `span l = (x₁, …, xₙ)`。 -/
def Ideal.span (l : List R) : Ideal R where
  carrier := InSpan l
  zero_mem := InSpan.zero
  add_mem := InSpan.add
  mul_mem r {a} ha := by
    induction ha with
    | zero => rw [mul_zero]; exact InSpan.zero
    | add _ _ iha ihb => rw [CommRing.mul_add]; exact InSpan.add iha ihb
    | smul s hx => rw [← CommRing.mul_assoc]; exact InSpan.smul (r * s) hx

/-- 有限生成イデアル。 -/
def Ideal.IsFG (I : Ideal R) : Prop := ∃ l : List R, ∀ a, a ∈ I ↔ InSpan l a
end Ideals

-- §§ spec
section Spectrum
variable (R : Type) [CommRing R]

/-- 素スペクトル `Spec R`。点は `R` の素イデアル。 -/
def PrimeSpectrum : Type := { P : Ideal R // P.IsPrime }

variable {R}

/-- 零点集合 `V(E) = { 𝔭 | E ⊆ 𝔭 }`。「E の元がすべて消える点」。 -/
def zeroLocus (E : R → Prop) : PrimeSpectrum R → Prop :=
  fun P => ∀ a, E a → a ∈ P.1

/-- 基本開集合 `D(f) = { 𝔭 | f ∉ 𝔭 }`。「f が消えない点」。 -/
def basicOpen (f : R) : PrimeSpectrum R → Prop :=
  fun P => f ∉ P.1

-- §§ spec_comap
/-- 環準同型 `φ : R → S` は、逆向きの写像 `Spec S → Spec R`, `𝔮 ↦ φ⁻¹(𝔮)` を誘導する。
素イデアルの逆像は素イデアル。矢印の向きが反転することに注意。 -/
def PrimeSpectrum.comap {S : Type} [CommRing S] (φ : R →ᵣ S) (Q : PrimeSpectrum S) : PrimeSpectrum R :=
  ⟨⟨fun a => φ a ∈ Q.1,
    by show φ 0 ∈ Q.1; rw [φ.map_zero]; exact Q.1.zero_mem,
    fun {a b} ha hb => by show φ (a + b) ∈ Q.1; rw [φ.map_add]; exact Q.1.add_mem ha hb,
    fun r {a} ha => by show φ (r * a) ∈ Q.1; rw [φ.map_mul]; exact Q.1.mul_mem _ ha⟩,
   ⟨fun h => Q.2.1 (by rw [← φ.map_one]; exact h),
    fun {a b} h => Q.2.2 (by rw [← φ.map_mul]; exact h)⟩⟩
end Spectrum

-- §§ topology
/-- 位相。「開集合」と呼ばれる部分集合の族で、全体・有限交叉・任意和で閉じるもの。
部分集合は述語 `X → Prop` で表す。 -/
structure Topology (X : Type) where
  IsOpen : (X → Prop) → Prop
  isOpen_univ : IsOpen (fun _ => True)
  isOpen_inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
  isOpen_sUnion : ∀ (𝒰 : (X → Prop) → Prop), (∀ U, 𝒰 U → IsOpen U) →
    IsOpen (fun x => ∃ U, 𝒰 U ∧ U x)

/-- 位相空間 = 型 + 位相。 -/
structure TopSpace where
  carrier : Type
  top : Topology carrier

instance : CoeSort TopSpace Type := ⟨TopSpace.carrier⟩

/-- 開集合の型。 -/
def Opens (X : TopSpace) : Type := { U : X → Prop // X.top.IsOpen U }

namespace Opens
variable {X : TopSpace}

instance : LE (Opens X) := ⟨fun V U => ∀ x, V.1 x → U.1 x⟩

theorem le_refl (U : Opens X) : U ≤ U := fun _ h => h
theorem le_trans {U V W : Opens X} (h₁ : W ≤ V) (h₂ : V ≤ U) : W ≤ U :=
  fun x h => h₂ x (h₁ x h)

/-- 二つの開集合の交わり。 -/
def inter (U V : Opens X) : Opens X :=
  ⟨fun x => U.1 x ∧ V.1 x, X.top.isOpen_inter U.2 V.2⟩

theorem inter_le_left (U V : Opens X) : inter U V ≤ U := fun _ h => h.1
theorem inter_le_right (U V : Opens X) : inter U V ≤ V := fun _ h => h.2

/-- 全体集合。 -/
def univ : Opens X := ⟨fun _ => True, X.top.isOpen_univ⟩
theorem le_univ (U : Opens X) : U ≤ univ := fun _ _ => trivial
end Opens

-- §§ zariski
/-- ザリスキ位相。閉集合を零点集合 `V(E)` とする。開集合は `V(E)` の補集合。 -/
def zariskiTopology (R : Type) [CommRing R] : Topology (PrimeSpectrum R) where
  IsOpen U := ∃ E : R → Prop, ∀ P, U P ↔ ¬ zeroLocus E P
  isOpen_univ := ⟨fun a => a = 1, fun P => by
    constructor
    · intro _ h; exact P.2.1 (h 1 rfl)
    · intro _; trivial⟩
  isOpen_inter := sorry   -- 演習: V(E) ∪ V(E') = V(E · E')
  isOpen_sUnion := sorry  -- 演習: ⋂ V(Eᵢ) = V(⋃ Eᵢ)

/-- 位相空間としての `Spec R`。 -/
def SpecTop (R : Type) [CommRing R] : TopSpace := ⟨PrimeSpectrum R, zariskiTopology R⟩

-- §§ continuous
/-- 連続写像。開集合の逆像が開集合。 -/
structure ContinuousMap (X Y : TopSpace) where
  toFun : X → Y
  isOpen_preimage : ∀ U : Opens Y, Y.top.IsOpen U.1 → X.top.IsOpen (fun x => U.1 (toFun x))

/-- 連続写像による開集合の逆像。 -/
def ContinuousMap.preimage {X Y : TopSpace} (f : ContinuousMap X Y) (U : Opens Y) : Opens X :=
  ⟨fun x => U.1 (f.toFun x), f.isOpen_preimage U U.2⟩

-- §§ localization
section Localization
variable {R : Type} [CommRing R]

/-- 乗法的部分集合。1 を含み、掛け算で閉じる。 -/
structure Submonoid (R : Type) [CommRing R] where
  carrier : R → Prop
  one_mem : carrier 1
  mul_mem : ∀ {a b}, carrier a → carrier b → carrier (a * b)

/-- 「分数」`a / s` の表示。分子 `a : R` と、分母 `s ∈ S`。 -/
structure Fraction (S : Submonoid R) where
  num : R
  den : R
  den_mem : S.carrier den

/-- 二つの分数が等しい: `a/s = b/t ⇔ ∃ u ∈ S, u (a t - b s) = 0`。 -/
def Fraction.rel {S : Submonoid R} (x y : Fraction S) : Prop :=
  ∃ u, S.carrier u ∧ u * (x.num * y.den + -(y.num * x.den)) = 0

/-- 局所化 `S⁻¹R`。分数の表示を、上の同値関係で割った商。 -/
def Localization (S : Submonoid R) : Type := Quot (Fraction.rel (S := S))

/-- 分数 `a / s` を局所化の元として見る。 -/
def Localization.mk {S : Submonoid R} (a s : R) (hs : S.carrier s) : Localization S :=
  Quot.mk _ ⟨a, s, hs⟩

-- §§ localization_ring
/-- 分数の足し算 `a/s + b/t = (at + bs)/(st)`。代表元の取り方によらないこと（`sorry`）は演習。 -/
def Localization.add {S : Submonoid R} : Localization S → Localization S → Localization S :=
  Quot.lift (fun x => Quot.lift
    (fun y => Localization.mk (x.num * y.den + y.num * x.den) (x.den * y.den) (S.mul_mem x.den_mem y.den_mem))
    sorry) sorry

/-- 分数の掛け算 `(a/s)(b/t) = ab/st`。 -/
def Localization.mul {S : Submonoid R} : Localization S → Localization S → Localization S :=
  Quot.lift (fun x => Quot.lift
    (fun y => Localization.mk (x.num * y.num) (x.den * y.den) (S.mul_mem x.den_mem y.den_mem))
    sorry) sorry

/-- `S⁻¹R` は可換環。公理の検証（`sorry`）は分数計算の演習。 -/
instance (S : Submonoid R) : CommRing (Localization S) where
  add := Localization.add
  mul := Localization.mul
  neg := Quot.lift (fun x => Localization.mk (-x.num) x.den x.den_mem) sorry
  zero := Localization.mk 0 1 S.one_mem
  one  := Localization.mk 1 1 S.one_mem
  add_assoc := sorry
  add_comm := sorry
  zero_add := sorry
  neg_add_cancel := sorry
  mul_assoc := sorry
  mul_comm := sorry
  one_mul := sorry
  mul_add := sorry

-- §§ localization_prime
/-- 素イデアルの補集合 `R ∖ 𝔭` は乗法的部分集合。 -/
def Ideal.primeCompl (P : Ideal R) (hP : P.IsPrime) : Submonoid R where
  carrier a := a ∉ P
  one_mem := hP.1
  mul_mem {a b} ha hb hab := by
    rcases hP.2 hab with h | h
    · exact ha h
    · exact hb h

/-- 素イデアル `𝔭` における局所化 `R_𝔭`。 -/
def localizationAt (P : PrimeSpectrum R) : Type := Localization (P.1.primeCompl P.2)

instance (P : PrimeSpectrum R) : CommRing (localizationAt P) :=
  inferInstanceAs (CommRing (Localization (P.1.primeCompl P.2)))

/-- べき `fⁿ`。 -/
def npow (f : R) : Nat → R
  | 0 => 1
  | n + 1 => npow f n * f

/-- `f` のべきからなる乗法的部分集合 `{1, f, f², …}`。 -/
def Submonoid.powers (f : R) : Submonoid R where
  carrier a := ∃ n : Nat, a = npow f n
  one_mem := ⟨0, rfl⟩
  mul_mem := sorry  -- 演習: fⁿ · fᵐ = fⁿ⁺ᵐ

/-- 標準的な写像 `R → S⁻¹R`, `a ↦ a / 1`。 -/
def Localization.algebraMap (S : Submonoid R) : R →ᵣ Localization S :=
  ⟨fun a => Localization.mk a 1 S.one_mem, sorry, sorry, rfl⟩

/-- `R[1/f]`。 -/
def Away (f : R) : Type := Localization (Submonoid.powers f)

end Localization

-- §§ presheaf
/-- 位相空間 `X` 上の（集合値の）前層。開集合ごとに「切断の集合」`obj U` を対応させ、
`V ⊆ U` に対して制限写像 `res : obj U → obj V` を与える。恒等と合成を保つ。 -/
structure Presheaf (X : TopSpace) where
  obj : Opens X → Type
  res : ∀ {U V : Opens X}, V ≤ U → obj U → obj V
  res_id : ∀ (U : Opens X) (s : obj U), res (Opens.le_refl U) s = s
  res_comp : ∀ {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : obj U),
    res h₂ (res h₁ s) = res (Opens.le_trans h₂ h₁) s

-- §§ sheaf
/-- 開被覆。`U` を覆う開集合の族 `V i ⊆ U`。 -/
structure OpenCover {X : TopSpace} (U : Opens X) where
  ι : Type
  V : ι → Opens X
  le : ∀ i, V i ≤ U
  covers : ∀ x, U.1 x → ∃ i, (V i).1 x

/-- 層。前層であって、「局所性」と「貼り合わせ」を満たすもの。 -/
structure Sheaf (X : TopSpace) extends Presheaf X where
  /-- 局所性: 各 `V i` への制限が一致する二つの切断は等しい。 -/
  locality : ∀ (U : Opens X) (𝒱 : OpenCover U) (s t : obj U),
    (∀ i, res (𝒱.le i) s = res (𝒱.le i) t) → s = t
  /-- 貼り合わせ: 交わりの上で一致する切断の族は、`U` 上の一つの切断から来る。 -/
  gluing : ∀ (U : Opens X) (𝒱 : OpenCover U) (s : ∀ i, obj (𝒱.V i)),
    (∀ i j, res (Opens.inter_le_left (𝒱.V i) (𝒱.V j)) (s i)
          = res (Opens.inter_le_right (𝒱.V i) (𝒱.V j)) (s j)) →
    ∃ t : obj U, ∀ i, res (𝒱.le i) t = s i

-- §§ stalk
section Stalk
variable {X : TopSpace} (F : Presheaf X) (x : X)

/-- 点 `x` の近傍で定義された切断 `(U, s)`。 -/
structure Germ where
  U : Opens X
  mem : U.1 x
  s : F.obj U

/-- 二つの切断が `x` の近くで一致する。 -/
def Germ.equiv (a b : Germ F x) : Prop :=
  ∃ (W : Opens X) (_ : W.1 x) (h₁ : W ≤ a.U) (h₂ : W ≤ b.U), F.res h₁ a.s = F.res h₂ b.s

/-- 茎 `F_x = colim_{U ∋ x} F(U)`。切断の芽（germ）全体。 -/
def Stalk : Type := Quot (Germ.equiv F x)

/-- 切断 `s ∈ F(U)` の `x` における芽。 -/
def Presheaf.germ {U : Opens X} (hx : U.1 x) (s : F.obj U) : Stalk F x :=
  Quot.mk _ ⟨U, hx, s⟩
end Stalk

-- §§ sheafofrings
/-- 環の層。各 `obj U` が可換環で、制限写像が環準同型。 -/
structure SheafOfRings (X : TopSpace) extends Sheaf X where
  ring : ∀ U, CommRing (obj U)
  res_add : ∀ {U V : Opens X} (h : V ≤ U) (s t : obj U), res h (s + t) = res h s + res h t
  res_mul : ∀ {U V : Opens X} (h : V ≤ U) (s t : obj U), res h (s * t) = res h s * res h t
  res_one : ∀ {U V : Opens X} (h : V ≤ U), res h (1 : obj U) = 1

attribute [instance] SheafOfRings.ring

/-- 制限写像を環準同型として取り出す。 -/
def SheafOfRings.resHom {X : TopSpace} (𝒪 : SheafOfRings X) {U V : Opens X} (h : V ≤ U) :
    𝒪.obj U →ᵣ 𝒪.obj V :=
  ⟨𝒪.res h, 𝒪.res_add h, 𝒪.res_mul h, 𝒪.res_one h⟩

/-- 環の層の茎は環になる（演習）。 -/
noncomputable instance {X : TopSpace} (𝒪 : SheafOfRings X) (x : X) :
    CommRing (Stalk 𝒪.toPresheaf x) := sorry

-- §§ specsheaf
section StructureSheaf
variable (R : Type) [CommRing R]

/-- 開集合 `U ⊆ Spec R` 上の「関数」: 各点 `𝔭 ∈ U` に `R_𝔭` の元を割り当てる写像であって、
局所的には一つの分数 `a / f` で書けるもの。 -/
def IsLocallyFraction (U : Opens (SpecTop R))
    (s : ∀ P : PrimeSpectrum R, U.1 P → localizationAt P) : Prop :=
  ∀ (P : PrimeSpectrum R) (_ : U.1 P),
    ∃ (V : Opens (SpecTop R)) (_ : V.1 P) (hVU : V ≤ U) (a f : R),
      ∀ (Q : PrimeSpectrum R) (hQ : V.1 Q),
        ∃ hf : f ∉ Q.1, s Q (hVU Q hQ) = Localization.mk a f hf

/-- `Spec R` の構造層 `𝒪_{Spec R}`。`𝒪(U)` は `U` 上の局所的に分数で書ける関数の環。 -/
noncomputable def specSheaf : SheafOfRings (SpecTop R) where
  obj U := { s : ∀ P : PrimeSpectrum R, U.1 P → localizationAt P // IsLocallyFraction R U s }
  res h s := ⟨fun P hP => s.1 P (h P hP), sorry⟩
  res_id := sorry
  res_comp := sorry
  locality := sorry
  gluing := sorry
  ring := sorry     -- 各点ごとの足し算・掛け算
  res_add := sorry
  res_mul := sorry
  res_one := sorry
end StructureSheaf

-- §§ ringedspace
/-- 環付き空間: 位相空間と、その上の環の層。 -/
structure RingedSpace where
  X : TopSpace
  𝒪 : SheafOfRings X

/-- 局所環付き空間: すべての茎 `𝒪_x` が局所環である環付き空間。 -/
structure LocallyRingedSpace extends RingedSpace where
  isLocal : ∀ x : X, IsLocalRing (Stalk 𝒪.toPresheaf x)

/-- アフィンスキーム `Spec R`（局所環付き空間として）。茎 `𝒪_𝔭 ≅ R_𝔭` が局所環であることは演習。 -/
noncomputable def Spec (R : Type) [CommRing R] : LocallyRingedSpace where
  X := SpecTop R
  𝒪 := specSheaf R
  isLocal := sorry

-- §§ lrshom
/-- 局所環付き空間の射 `(f, f♯) : X → Y`。
連続写像 `f` と、各開集合 `V ⊆ Y` ごとの環準同型 `f♯_V : 𝒪_Y(V) → 𝒪_X(f⁻¹V)`。
制限と両立し、茎に誘導される準同型 `𝒪_{Y,f(x)} → 𝒪_{X,x}` が局所準同型。 -/
structure LRSHom (X Y : LocallyRingedSpace) where
  base : ContinuousMap X.X Y.X
  sharp : ∀ V : Opens Y.X, Y.𝒪.obj V →ᵣ X.𝒪.obj (base.preimage V)
  sharp_res : ∀ {V W : Opens Y.X} (h : W ≤ V) (s : Y.𝒪.obj V),
    X.𝒪.res (fun _ hx => h _ hx) (sharp V s) = sharp W (Y.𝒪.res h s)
  stalk_local : ∀ (x : X.X) (V : Opens Y.X) (hx : V.1 (base.toFun x)) (s : Y.𝒪.obj V),
    IsUnit (X.𝒪.germ x hx (sharp V s)) → IsUnit (Y.𝒪.germ (base.toFun x) hx s)

infixr:10 " ⟶ " => LRSHom

/-- 恒等射。 -/
def LRSHom.id (X : LocallyRingedSpace) : X ⟶ X where
  base := ⟨fun x => x, fun U hU => hU⟩
  sharp V := RingHom.id _
  sharp_res := sorry
  stalk_local := sorry

/-- 合成。 -/
def LRSHom.comp {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z where
  base := ⟨fun x => g.base.toFun (f.base.toFun x), sorry⟩
  sharp W := RingHom.comp (f.sharp (g.base.preimage W)) (g.sharp W)
  sharp_res := sorry
  stalk_local := sorry

/-- 同型。互いに逆な射の組。 -/
structure LRSIso (X Y : LocallyRingedSpace) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv : LRSHom.comp hom inv = LRSHom.id X
  inv_hom : LRSHom.comp inv hom = LRSHom.id Y

-- §§ restrict
section Restrict
variable (X : LocallyRingedSpace) (U : Opens X.X)

/-- 開集合 `U` を部分空間として位相空間にする。 -/
def Opens.toTopSpace : TopSpace where
  carrier := { x : X.X // U.1 x }
  top :=
    { IsOpen := fun V => ∃ W : Opens X.X, ∀ x, V x ↔ W.1 x.1
      isOpen_univ := ⟨Opens.univ, fun _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
      isOpen_inter := sorry
      isOpen_sUnion := sorry }

/-- 部分空間 `U` の開集合を `X` の開集合として見る（`U` が開なので開になる）。 -/
def Opens.ofSub (V : Opens (Opens.toTopSpace X U)) : Opens X.X :=
  ⟨fun x => ∃ h : U.1 x, V.1 ⟨x, h⟩, sorry⟩

/-- 局所環付き空間を開集合 `U` に制限したもの `(U, 𝒪_X|_U)`。 -/
noncomputable def LocallyRingedSpace.restrict : LocallyRingedSpace where
  X := Opens.toTopSpace X U
  𝒪 := { obj := fun V => X.𝒪.obj (Opens.ofSub X U V),
          res := fun h s => X.𝒪.res (sorry) s,
          res_id := sorry, res_comp := sorry, locality := sorry, gluing := sorry,
          ring := fun _ => X.𝒪.ring _,
          res_add := sorry, res_mul := sorry, res_one := sorry }
  isLocal := sorry
end Restrict

-- §§ scheme
/-- スキーム。局所環付き空間であって、各点が、あるアフィンスキーム `Spec R` と同型な
開近傍を持つもの。 -/
structure Scheme extends LocallyRingedSpace where
  local_affine : ∀ x : X, ∃ (U : Opens X) (_ : U.1 x) (R : Type) (_ : CommRing R),
    Nonempty (LRSIso (toLocallyRingedSpace.restrict U) (Spec R))

/-- スキームの射は局所環付き空間の射。 -/
def Scheme.Hom (X Y : Scheme) : Type := X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace

/-- アフィン開集合: `U` の上への制限が、ある `Spec R` と同型。 -/
def Scheme.IsAffineOpen (X : Scheme) (U : Opens X.X) : Prop :=
  ∃ (R : Type) (_ : CommRing R), Nonempty (LRSIso (X.toLocallyRingedSpace.restrict U) (Spec R))

/-- `f : X → Y`、`U ⊆ Y`、`V ⊆ f⁻¹U` に対する環準同型 `𝒪_Y(U) → 𝒪_X(f⁻¹U) → 𝒪_X(V)`。 -/
def Scheme.Hom.appLE {X Y : Scheme} (f : Scheme.Hom X Y) (U : Opens Y.X) (V : Opens X.X)
    (h : V ≤ f.base.preimage U) : Y.𝒪.obj U →ᵣ X.𝒪.obj V :=
  RingHom.comp (X.𝒪.resHom h) (f.sharp U)

-- §§ category
universe u

/-- （小さいとは限らない）圏。対象の型、射の型、恒等射、合成、公理。 -/
structure Category where
  Obj : Type u
  Hom : Obj → Obj → Type
  id : ∀ X, Hom X X
  comp : ∀ {X Y Z}, Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

-- §§ sieve
section Sieves
variable {C : Category.{u}}

/-- 対象 `U` 上の篩（ふるい）。`U` に向かう射の集まりで、前から射を合成しても閉じているもの。
「開集合 U の部分開集合の族で、さらに小さい開集合を取っても閉じているもの」の一般化。 -/
structure Sieve (U : C.Obj) where
  arrows : ∀ {V : C.Obj}, C.Hom V U → Prop
  downward_closed : ∀ {V W : C.Obj} {f : C.Hom V U}, arrows f → ∀ (g : C.Hom W V), arrows (C.comp g f)

/-- 篩の引き戻し `f⁎S = { g | g ≫ f ∈ S }`。「開集合の族を f⁻¹ で引き戻す」に対応。 -/
def Sieve.pullback {U V : C.Obj} (S : Sieve U) (f : C.Hom V U) : Sieve V where
  arrows g := S.arrows (C.comp g f)
  downward_closed {_ _ g} hg h := by
    show S.arrows (C.comp (C.comp h g) f)
    rw [C.assoc]; exact S.downward_closed hg h

/-- 最大の篩: すべての射。 -/
def Sieve.top (U : C.Obj) : Sieve U := ⟨fun _ => True, fun _ _ => trivial⟩

-- §§ grothendieck
/-- グロタンディーク位相。各対象 `U` に「被覆篩」の集まり `covering U` を指定したもので、
(T1) 最大篩は被覆、(T2) 被覆篩の引き戻しは被覆、(T3) 局所的に被覆なら被覆、を満たす。 -/
structure GrothendieckTopology (C : Category.{u}) where
  covering : ∀ (U : C.Obj), Sieve U → Prop
  top_mem : ∀ U, covering U (Sieve.top U)
  pullback_stable : ∀ {U V : C.Obj} (S : Sieve U) (f : C.Hom V U), covering U S → covering V (S.pullback f)
  transitive : ∀ {U : C.Obj} (S : Sieve U) (T : Sieve U), covering U S →
    (∀ {V : C.Obj} (f : C.Hom V U), S.arrows f → covering V (T.pullback f)) → covering U T
end Sieves

-- §§ sitesheaf
/-- サイト = 圏 + グロタンディーク位相。 -/
structure Site where
  C : Category.{u}
  J : GrothendieckTopology C

section SiteSheaf
variable {C : Category.{u}}

-- §§ cpresheaf
/-- 圏 `C` 上の（集合値の）前層。反変関手 `Cᵒᵖ → Set`。 -/
structure CPresheaf (C : Category.{u}) where
  obj : C.Obj → Type
  map : ∀ {U V : C.Obj}, C.Hom V U → obj U → obj V
  map_id : ∀ (U : C.Obj) (s : obj U), map (C.id U) s = s
  map_comp : ∀ {U V W : C.Obj} (f : C.Hom V U) (g : C.Hom W V) (s : obj U),
    map g (map f s) = map (C.comp g f) s

-- §§ sheafcondition
/-- 篩 `S` に沿った「切断の族」: `S` に属する各射 `f : V → U` に切断 `x f ∈ F(V)` を割り当てたもの。 -/
def FamilyOfElements (F : CPresheaf C) {U : C.Obj} (S : Sieve U) : Type u :=
  ∀ {V : C.Obj} (f : C.Hom V U), S.arrows f → F.obj V

/-- 両立する族: 射をさらに合成しても割り当てが整合する（開集合の言葉では「交わりの上で一致」）。 -/
def FamilyOfElements.Compatible {F : CPresheaf C} {U : C.Obj} {S : Sieve U}
    (x : FamilyOfElements F S) : Prop :=
  ∀ {V W : C.Obj} (f : C.Hom V U) (hf : S.arrows f) (g : C.Hom W V),
    F.map g (x f hf) = x (C.comp g f) (S.downward_closed hf g)

/-- `t ∈ F(U)` が族 `x` の貼り合わせ（融合）であること。 -/
def FamilyOfElements.IsAmalgamation {F : CPresheaf C} {U : C.Obj} {S : Sieve U}
    (x : FamilyOfElements F S) (t : F.obj U) : Prop :=
  ∀ {V : C.Obj} (f : C.Hom V U) (hf : S.arrows f), F.map f t = x f hf

/-- 前層 `F` が篩 `S` について層条件を満たす: 両立する族はただ一つの貼り合わせを持つ。 -/
def IsSheafFor (F : CPresheaf C) {U : C.Obj} (S : Sieve U) : Prop :=
  ∀ x : FamilyOfElements F S, x.Compatible →
    ∃ t : F.obj U, x.IsAmalgamation t ∧ ∀ t', x.IsAmalgamation t' → t' = t

/-- サイト上の層: すべての被覆篩について層条件を満たす前層。 -/
structure CSheaf (𝒳 : Site.{u}) extends CPresheaf 𝒳.C where
  isSheaf : ∀ (U : 𝒳.C.Obj) (S : Sieve U), 𝒳.J.covering U S → IsSheafFor toCPresheaf S
end SiteSheaf

-- §§ algebra
section Algebras
variable {R : Type} [CommRing R]

/-- `R`-代数: 可換環 `A` と環準同型 `R → A`（構造射）。 -/
structure Algebra (R A : Type) [CommRing R] [CommRing A] where
  algebraMap : R →ᵣ A

/-- `R`-代数の準同型: 構造射と両立する環準同型。 -/
structure AlgHom {A B : Type} [CommRing A] [CommRing B] (𝒜 : Algebra R A) (ℬ : Algebra R B) where
  toRingHom : A →ᵣ B
  commutes : ∀ r, toRingHom (𝒜.algebraMap r) = ℬ.algebraMap r

-- §§ squarezero
/-- 「二乗零の核を持つ全射」: `π : B → C` 全射で、`ker π · ker π = 0`。
`C = B / I`, `I² = 0` という状況を、商環を構成せずに表現している。 -/
structure SquareZeroExt {B C : Type} [CommRing B] [CommRing C] (π : B →ᵣ C) : Prop where
  surj : Function.Surjective π.toFun
  sq_zero : ∀ a b, π a = 0 → π b = 0 → a * b = 0

/-- 形式的エタール: 任意の二乗零拡大 `π : B → C` に対し、`A → C` は `A → B` にただ一通りに持ち上がる。
図式: A ⟶ C を、A ⟶ B ⟶ C と分解する仕方が「ちょうど一つ」。 -/
def Algebra.FormallyEtale {A : Type} [CommRing A] (𝒜 : Algebra R A) : Prop :=
  ∀ (B C : Type) [CommRing B] [CommRing C] (ℬ : Algebra R B) (𝒞 : Algebra R C)
    (π : AlgHom ℬ 𝒞), SquareZeroExt π.toRingHom →
    ∀ (g : AlgHom 𝒜 𝒞),
      ∃ (f : AlgHom 𝒜 ℬ), (∀ a, π.toRingHom (f.toRingHom a) = g.toRingHom a) ∧
        ∀ (f' : AlgHom 𝒜 ℬ), (∀ a, π.toRingHom (f'.toRingHom a) = g.toRingHom a) → f' = f

/-- 形式的不分岐: 持ち上げは高々一つ。 -/
def Algebra.FormallyUnramified {A : Type} [CommRing A] (𝒜 : Algebra R A) : Prop :=
  ∀ (B C : Type) [CommRing B] [CommRing C] (ℬ : Algebra R B) (𝒞 : Algebra R C)
    (π : AlgHom ℬ 𝒞), SquareZeroExt π.toRingHom →
    ∀ (f₁ f₂ : AlgHom 𝒜 ℬ), (∀ a, π.toRingHom (f₁.toRingHom a) = π.toRingHom (f₂.toRingHom a)) → f₁ = f₂

/-- 形式的スムーズ: 持ち上げが少なくとも一つ。 -/
def Algebra.FormallySmooth {A : Type} [CommRing A] (𝒜 : Algebra R A) : Prop :=
  ∀ (B C : Type) [CommRing B] [CommRing C] (ℬ : Algebra R B) (𝒞 : Algebra R C)
    (π : AlgHom ℬ 𝒞), SquareZeroExt π.toRingHom →
    ∀ (g : AlgHom 𝒜 𝒞), ∃ (f : AlgHom 𝒜 ℬ), ∀ a, π.toRingHom (f.toRingHom a) = g.toRingHom a
end Algebras

-- §§ freealgebra
section FreeAlgebra
variable (R : Type) [CommRing R] (n : Nat)

/-- 多項式の「式」。変数 `Xᵢ`、定数、和、積、マイナスから作られる項。 -/
inductive Term
  | var : Fin n → Term
  | const : R → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | neg : Term → Term

/-- 式の間の同値関係: 可換環の公理と「定数は環準同型」で生成される最小の合同関係。
`R[X₁,…,Xₙ]` はこれで式を割ったもの。 -/
inductive Term.Rel : Term R n → Term R n → Prop
  | refl (t) : Rel t t
  | symm {s t} : Rel s t → Rel t s
  | trans {s t u} : Rel s t → Rel t u → Rel s u
  | add_congr {s s' t t'} : Rel s s' → Rel t t' → Rel (.add s t) (.add s' t')
  | mul_congr {s s' t t'} : Rel s s' → Rel t t' → Rel (.mul s t) (.mul s' t')
  | neg_congr {s s'} : Rel s s' → Rel (.neg s) (.neg s')
  | add_assoc (a b c) : Rel (.add (.add a b) c) (.add a (.add b c))
  | add_comm (a b) : Rel (.add a b) (.add b a)
  | zero_add (a) : Rel (.add (.const 0) a) a
  | neg_add_cancel (a) : Rel (.add (.neg a) a) (.const 0)
  | mul_assoc (a b c) : Rel (.mul (.mul a b) c) (.mul a (.mul b c))
  | mul_comm (a b) : Rel (.mul a b) (.mul b a)
  | one_mul (a) : Rel (.mul (.const 1) a) a
  | mul_add (a b c) : Rel (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  | const_add (r s : R) : Rel (.const (r + s)) (.add (.const r) (.const s))
  | const_mul (r s : R) : Rel (.const (r * s)) (.mul (.const r) (.const s))

/-- 多項式環 `R[X₁, …, Xₙ]`。式を同値関係で割ったもの。 -/
def FreeCommAlg : Type := Quot (Term.Rel R n)

/-- `R[X₁,…,Xₙ]` は可換環（演習: 各演算が同値関係と両立し、公理は `Rel` の生成元から出る）。 -/
noncomputable instance : CommRing (FreeCommAlg R n) := sorry

/-- 構造射 `R → R[X₁,…,Xₙ]`, `r ↦ 定数 r`。 -/
noncomputable def FreeCommAlg.algebra : Algebra R (FreeCommAlg R n) := ⟨⟨fun r => Quot.mk _ (.const r), sorry, sorry, sorry⟩⟩

end FreeAlgebra

-- §§ etale_alg
section Etale
variable {R : Type} [CommRing R]

/-- 有限表示: 有限変数の多項式環からの全射で、核が有限生成のもの。
`A ≅ R[X₁,…,Xₙ] / (f₁,…,fₘ)`。 -/
def Algebra.FinitePresentation {A : Type} [CommRing A] (𝒜 : Algebra R A) : Prop :=
  ∃ (n : Nat) (φ : AlgHom (FreeCommAlg.algebra R n) 𝒜),
    Function.Surjective φ.toRingHom.toFun ∧ φ.toRingHom.ker.IsFG

/-- エタール代数 = 形式的エタール + 有限表示。 -/
def Algebra.Etale {A : Type} [CommRing A] (𝒜 : Algebra R A) : Prop :=
  𝒜.FormallyEtale ∧ 𝒜.FinitePresentation

/-- 環準同型 `φ : R → S` がエタール: `S` を `φ` で `R`-代数と見てエタール。 -/
def RingHom.IsEtale {S : Type} [CommRing S] (φ : R →ᵣ S) : Prop :=
  Algebra.Etale (⟨φ⟩ : Algebra R S)

/-- 恒等写像はエタール。 -/
theorem RingHom.id_isEtale : (RingHom.id R).IsEtale := sorry

/-- 例: 局所化 `R → R[1/f]` はエタール（開埋め込み `D(f) ↪ Spec R` に対応）。 -/
theorem localization_isEtale (f : R) : (Localization.algebraMap (Submonoid.powers f)).IsEtale := sorry
end Etale

-- §§ etalemorphism
/-- スキームの射 `f : X → Y` がエタール: `Y` のアフィン開集合 `U` と、`f⁻¹U` に含まれる `X` の
アフィン開集合 `V` のすべてについて、環準同型 `𝒪_Y(U) → 𝒪_X(V)` がエタール。 -/
def Scheme.Hom.IsEtale {X Y : Scheme} (f : Scheme.Hom X Y) : Prop :=
  ∀ (U : Opens Y.X) (V : Opens X.X) (h : V ≤ f.base.preimage U),
    Y.IsAffineOpen U → X.IsAffineOpen V → (f.appLE U V h).IsEtale

/-- 恒等射はエタール（演習: `R → R` は形式的エタールかつ有限表示）。 -/
theorem Scheme.id_isEtale (X : Scheme) :
    Scheme.Hom.IsEtale (X := X) (Y := X) (LRSHom.id X.toLocallyRingedSpace) := sorry

-- §§ etalesite
/-- `X` 上エタールなスキーム `(U, f : U → X)`。小エタールサイトの対象。 -/
structure EtaleOver (X : Scheme) where
  U : Scheme
  f : Scheme.Hom U X
  etale : f.IsEtale

/-- `X` 上の射: `X` への射と両立するスキームの射。 -/
structure EtaleOver.Hom {X : Scheme} (V U : EtaleOver X) where
  g : Scheme.Hom V.U U.U
  w : LRSHom.comp g U.f = V.f

/-- `X` 上エタールなスキームの圏 `Ét(X)`。 -/
noncomputable abbrev etaleCategory (X : Scheme) : Category.{1} where
  Obj := EtaleOver X
  Hom := EtaleOver.Hom
  id U := ⟨LRSHom.id _, sorry⟩
  comp g h := ⟨LRSHom.comp g.g h.g, sorry⟩
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

-- §§ etaletopology
/-- エタール位相。`U` 上の篩が被覆 ⇔ 篩に属する射たちの像が `U` を覆う（jointly surjective）。 -/
noncomputable def etaleTopology (X : Scheme) : GrothendieckTopology (etaleCategory X) where
  covering U S := ∀ x : U.U.X, ∃ (V : EtaleOver X) (g : EtaleOver.Hom V U) (y : V.U.X),
    S.arrows g ∧ g.g.base.toFun y = x
  top_mem := sorry          -- 恒等射一本で覆える
  pullback_stable := sorry  -- 定理: エタール射はファイバー積で保たれ、全射性も保たれる
  transitive := sorry       -- 被覆の被覆は被覆

/-- 小エタールサイト `X_ét`。 -/
noncomputable abbrev etaleSite (X : Scheme) : Site.{1} := ⟨etaleCategory X, etaleTopology X⟩

/-- `X` 自身（恒等射）はエタールサイトの終対象。層の「大域切断」はここでの値。 -/
noncomputable def EtaleOver.self (X : Scheme) : EtaleOver X := ⟨X, LRSHom.id _, X.id_isEtale⟩

-- §§ abgroup
/-- アーベル群。 -/
class AddCommGroup (A : Type) extends Add A, Neg A, Zero A where
  add_assoc : ∀ a b c : A, a + b + c = a + (b + c)
  add_comm  : ∀ a b : A, a + b = b + a
  zero_add  : ∀ a : A, 0 + a = a
  neg_add_cancel : ∀ a : A, -a + a = 0

/-- 可換環は（足し算について）アーベル群。 -/
instance {R : Type} [CommRing R] : AddCommGroup R where
  add_assoc := CommRing.add_assoc
  add_comm := CommRing.add_comm
  zero_add := CommRing.zero_add
  neg_add_cancel := CommRing.neg_add_cancel

/-- アーベル群の準同型。 -/
structure AddHom (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  toFun : A → B
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b

instance {A B : Type} [AddCommGroup A] [AddCommGroup B] : CoeFun (AddHom A B) (fun _ => A → B) :=
  ⟨AddHom.toFun⟩

-- §§ absheaf
section AbelianSheaves
variable {𝒳 : Site.{u}}

/-- アーベル群の前層: 各対象にアーベル群、各射に群準同型。 -/
structure AbPresheaf (C : Category.{u}) where
  obj : C.Obj → Type
  grp : ∀ U, AddCommGroup (obj U)
  map : ∀ {U V : C.Obj}, C.Hom V U → obj U → obj V
  map_add : ∀ {U V : C.Obj} (f : C.Hom V U) (s t : obj U), map f (s + t) = map f s + map f t
  map_id : ∀ (U : C.Obj) (s : obj U), map (C.id U) s = s
  map_comp : ∀ {U V W : C.Obj} (f : C.Hom V U) (g : C.Hom W V) (s : obj U),
    map g (map f s) = map (C.comp g f) s

attribute [instance] AbPresheaf.grp

/-- 群構造を忘れて集合値の前層と見る。 -/
def AbPresheaf.toCPresheaf {C : Category.{u}} (F : AbPresheaf C) : CPresheaf C :=
  ⟨F.obj, F.map, F.map_id, F.map_comp⟩

/-- サイト上のアーベル群の層。 -/
structure AbSheaf (𝒳 : Site.{u}) extends AbPresheaf 𝒳.C where
  isSheaf : ∀ (U : 𝒳.C.Obj) (S : Sieve U), 𝒳.J.covering U S → IsSheafFor toAbPresheaf.toCPresheaf S

/-- アーベル層の射: 各対象で群準同型、制限と両立（自然変換）。 -/
structure AbSheaf.Hom (F G : AbSheaf 𝒳) where
  app : ∀ U, F.obj U → G.obj U
  app_add : ∀ U (a b : F.obj U), app U (a + b) = app U a + app U b
  naturality : ∀ {U V : 𝒳.C.Obj} (f : 𝒳.C.Hom V U) (s : F.obj U), app V (F.map f s) = G.map f (app U s)

/-- 零射。 -/
def AbSheaf.Hom.zero (F G : AbSheaf 𝒳) : F.Hom G := ⟨fun _ _ => 0, sorry, sorry⟩

-- §§ exact
/-- 単射（モノ射）: 各対象の上で単射。 -/
def AbSheaf.Hom.IsMono {F G : AbSheaf 𝒳} (φ : F.Hom G) : Prop :=
  ∀ U, Function.Injective (φ.app U)

/-- `F →φ→ G →ψ→ H` が `G` で完全。
(1) `ψ ∘ φ = 0`、(2) `ψ(s) = 0` なる切断 `s ∈ G(U)` は、`U` のある被覆の上で局所的に `φ` の像に入る。
（層の圏では「像 = 核」を各切断ごとには要求できないので、被覆の上での持ち上げで言い換える。） -/
def AbSheaf.IsExactAt {F G H : AbSheaf 𝒳} (φ : F.Hom G) (ψ : G.Hom H) : Prop :=
  (∀ U (s : F.obj U), ψ.app U (φ.app U s) = 0) ∧
  ∀ (U : 𝒳.C.Obj) (s : G.obj U), ψ.app U s = 0 →
    ∃ S : Sieve U, 𝒳.J.covering U S ∧
      ∀ {V : 𝒳.C.Obj} (f : 𝒳.C.Hom V U), S.arrows f → ∃ t : F.obj V, φ.app V t = G.map f s

-- §§ injective
/-- 入射的対象: 単射 `A ↪ B` に沿って、`A → I` はいつでも `B → I` に延長できる。 -/
def AbSheaf.IsInjective (I : AbSheaf 𝒳) : Prop :=
  ∀ (A B : AbSheaf 𝒳) (ι : A.Hom B), ι.IsMono →
    ∀ (α : A.Hom I), ∃ β : B.Hom I, ∀ U (a : A.obj U), β.app U (ι.app U a) = α.app U a

/-- 入射的分解 `0 → F → I⁰ → I¹ → I² → ⋯`（完全列で、各 `Iⁿ` が入射的）。 -/
structure InjectiveResolution (F : AbSheaf 𝒳) where
  I : Nat → AbSheaf 𝒳
  injective : ∀ n, (I n).IsInjective
  ε : F.Hom (I 0)
  d : ∀ n, (I n).Hom (I (n + 1))
  ε_mono : ε.IsMono
  exact₀ : AbSheaf.IsExactAt ε (d 0)
  exact : ∀ n, AbSheaf.IsExactAt (d n) (d (n + 1))
end AbelianSheaves

-- §§ complex
/-- アーベル群の余鎖複体 `A⁰ → A¹ → A² → ⋯`, `d ∘ d = 0`。 -/
structure Cocomplex where
  A : Nat → Type
  grp : ∀ n, AddCommGroup (A n)
  d : ∀ n, AddHom (A n) (A (n + 1))
  d_d : ∀ n (a : A n), d (n + 1) (d n a) = 0

attribute [instance] Cocomplex.grp

namespace Cocomplex
variable (K : Cocomplex)

/-- 余輪体 `Zⁿ = ker dⁿ`。 -/
def Cocycles (n : Nat) : Type := { a : K.A n // K.d n a = 0 }

/-- 余境界 `Bⁿ = im dⁿ⁻¹`（`n = 0` では `0`）。 -/
def IsCoboundary : ∀ n : Nat, K.A n → Prop
  | 0 => fun a => a = 0
  | n + 1 => fun a => ∃ b : K.A n, K.d n b = a

/-- コホモロジー `Hⁿ(K) = Zⁿ / Bⁿ`。二つの余輪体は差が余境界なら同一視する。 -/
def H (n : Nat) : Type :=
  Quot (fun a b : K.Cocycles n => K.IsCoboundary n (a.1 + -b.1))
end Cocomplex

-- §§ globalsections
/-- 入射的分解の各項を `X` 自身で評価した複体 `Γ(X, I⁰) → Γ(X, I¹) → ⋯`。 -/
noncomputable def globalSections {X : Scheme} {F : AbSheaf (etaleSite X)}
    (I : InjectiveResolution F) : Cocomplex where
  A n := (I.I n).obj (EtaleOver.self X)
  grp n := (I.I n).grp _
  d n := ⟨(I.d n).app _, (I.d n).app_add _⟩
  d_d n a := (I.exact n).1 _ a

-- §§ definition
/-- 定理（十分な入射的対象の存在）: すべてのアーベル層は入射的分解を持つ。 -/
theorem exists_injectiveResolution {X : Scheme} (F : AbSheaf (etaleSite X)) :
    Nonempty (InjectiveResolution F) := sorry

/-- **エタール・コホモロジー** `Hⁿ(X_ét, F)`。
入射的分解 `F → I•` を一つ選び、大域切断の複体 `Γ(X, I•)` の `n` 次コホモロジーを取る。 -/
noncomputable def etaleCohomology (X : Scheme) (F : AbSheaf (etaleSite X)) (n : Nat) : Type :=
  (globalSections (Classical.choice (exists_injectiveResolution F))).H n

-- §§ theorems
/-- 二つの型の間の全単射。 -/
structure Bijection (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- 定理（分解の取り方によらない）: 別の入射的分解を使っても同じ群が得られる。 -/
theorem etaleCohomology_independent {X : Scheme} (F : AbSheaf (etaleSite X)) (n : Nat)
    (I I' : InjectiveResolution F) :
    Nonempty (Bijection ((globalSections I).H n) ((globalSections I').H n)) := sorry

/-- 定理: `H⁰(X_ét, F) = F(X)`（大域切断）。 -/
theorem etaleCohomology_zero (X : Scheme) (F : AbSheaf (etaleSite X)) :
    Nonempty (Bijection (etaleCohomology X F 0) (F.obj (EtaleOver.self X))) := sorry

-- §§ coefficients
section Coefficients
variable (X : Scheme)

/-- 局所定数関数: 各点の近傍で一定。 -/
def IsLocallyConstant {T : TopSpace} {α : Type} (s : T → α) : Prop :=
  ∀ x, ∃ W : Opens T, W.1 x ∧ ∀ y, W.1 y → s y = s x

/-- 定数層 `ℤ/nℤ`: `U ↦ { U → ℤ/nℤ : 局所定数 }`。 `Fin n` を `ℤ/nℤ` として使う。 -/
noncomputable def constantSheaf (n : Nat) : AbSheaf (etaleSite X) where
  obj (U : EtaleOver X) := { s : U.U.X → Fin (n + 1) // IsLocallyConstant s }
  grp _ := sorry
  map {U V : EtaleOver X} (g : EtaleOver.Hom V U) s := ⟨fun y => s.1 (g.g.base.toFun y), sorry⟩
  map_add := sorry
  map_id := sorry
  map_comp := sorry
  isSheaf := sorry  -- 定理: 局所定数関数はエタール被覆に沿って貼り合う

-- §§ gm
/-- 乗法群 `𝔾ₘ`: `U ↦ 𝒪(U)ˣ`。群演算は掛け算。 -/
noncomputable def Gm : AbSheaf (etaleSite X) where
  obj (U : EtaleOver X) := { a : U.U.𝒪.obj Opens.univ // IsUnit a }
  grp _ := sorry    -- 単元群（掛け算をアーベル群の「+」として使う）
  map {U V : EtaleOver X} (g : EtaleOver.Hom V U) a := ⟨g.g.sharp Opens.univ a.1, sorry⟩
  map_add := sorry
  map_id := sorry
  map_comp := sorry
  isSheaf := sorry  -- 定理（エタール降下）: `𝒪` はエタール位相で層

/-- 自然数 `n` を環の元 `n · 1` と見る。 -/
def ofNat' {R : Type} [CommRing R] : Nat → R
  | 0 => 0
  | n + 1 => ofNat' n + 1

/-- `n` 乗写像 `𝔾ₘ → 𝔾ₘ`。 -/
noncomputable def Gm.pow (n : Nat) : (Gm X).Hom (Gm X) := ⟨fun U a => ⟨npow a.1 n, sorry⟩, sorry, sorry⟩

/-- `n` 乗根の層 `μₙ = ker(𝔾ₘ →ⁿ 𝔾ₘ)`。 -/
noncomputable def mu (n : Nat) : AbSheaf (etaleSite X) where
  obj (U : EtaleOver X) := { a : (Gm X).obj U // npow a.1 n = 1 }
  grp _ := sorry
  map {U V : EtaleOver X} (g : EtaleOver.Hom V U) a := ⟨(Gm X).map g a.1, sorry⟩
  map_add := sorry
  map_id := sorry
  map_comp := sorry
  isSheaf := sorry

/-- 包含 `μₙ → 𝔾ₘ`。 -/
noncomputable def mu.incl (n : Nat) : (mu X n).Hom (Gm X) := ⟨fun _ a => a.1, sorry, sorry⟩

-- §§ kummer
/-- **Kummer 完全列** `0 → μₙ → 𝔾ₘ →ⁿ 𝔾ₘ → 0`（`n` が `X` 上可逆のとき、エタール位相で完全）。 -/
theorem kummer_exact (n : Nat) (hn : IsUnit (ofNat' n : X.𝒪.obj Opens.univ)) :
    (mu.incl X n).IsMono ∧ AbSheaf.IsExactAt (mu.incl X n) (Gm.pow X n) ∧
    ∀ (U : EtaleOver X) (a : (Gm X).obj U), ∃ S : Sieve U, (etaleTopology X).covering U S ∧
      ∀ {V : EtaleOver X} (f : EtaleOver.Hom V U), S.arrows (C := etaleCategory X) f →
        ∃ b : (Gm X).obj V, (Gm.pow X n).app V b = (Gm X).map f a := sorry
end Coefficients

end Tutorial
