import EAQECC.Symplectic.Decomposition

/-!
辛子空间的辅助扩展。将非退化部分的辛内积在辅助坐标上补偿，
得到全迷向的扩展子空间，并证明投影恢复原空间、辅助坐标为零的部分恢复根空间。
-/

namespace Quantum

/- 发送端与辅助端的坐标划分、补零嵌入和发送端投影。
以下坐标引理说明各映射的取值、单射性以及投影恢复关系。
-/
private def baseSymplecticCoordinateEmbedding (n c : ℕ) :
    Fin (n + n) → Fin ((n + c) + (n + c)) :=
  fun j =>
    Fin.addCases
      (fun i : Fin n =>
        Fin.castAdd (n + c) (Fin.castAdd c i))
      (fun i : Fin n =>
        Fin.natAdd (n + c) (Fin.castAdd c i))
      j

private def baseSymplecticCoordinate? (n c : ℕ) :
    Fin ((n + c) + (n + c)) → Option (Fin (n + n)) :=
  fun j =>
    Fin.addCases
      (fun q : Fin (n + c) =>
        Fin.addCases
          (fun i : Fin n => some (Fin.castAdd n i))
          (fun _ : Fin c => none)
          q)
      (fun q : Fin (n + c) =>
        Fin.addCases
          (fun i : Fin n => some (Fin.natAdd n i))
          (fun _ : Fin c => none)
          q)
      j

private def auxiliarySymplecticCoordinate? (n c : ℕ) :
    Fin ((n + c) + (n + c)) → Option (Fin (c + c)) :=
  fun j =>
    Fin.addCases
      (fun q : Fin (n + c) =>
        Fin.addCases
          (fun _ : Fin n => none)
          (fun i : Fin c => some (Fin.castAdd c i))
          q)
      (fun q : Fin (n + c) =>
        Fin.addCases
          (fun _ : Fin n => none)
          (fun i : Fin c => some (Fin.natAdd c i))
          q)
      j

def baseSymplecticEmbedding (n c : ℕ) :
    BinarySymplecticVector n →ₗ[ZMod 2] BinarySymplecticVector (n + c) :=
  LinearMap.pi fun j =>
    match baseSymplecticCoordinate? n c j with
    | some i => LinearMap.proj (R := ZMod 2) i
    | none => 0

def baseSymplecticProjection (n c : ℕ) :
    BinarySymplecticVector (n + c) →ₗ[ZMod 2] BinarySymplecticVector n :=
  LinearMap.pi fun j =>
    LinearMap.proj (R := ZMod 2)
      (baseSymplecticCoordinateEmbedding n c j)

def auxiliarySymplecticEmbedding (n c : ℕ) :
    BinarySymplecticVector c →ₗ[ZMod 2] BinarySymplecticVector (n + c) :=
  LinearMap.pi fun j =>
    match auxiliarySymplecticCoordinate? n c j with
    | some i => LinearMap.proj (R := ZMod 2) i
    | none => 0

@[simp]
theorem baseSymplecticEmbedding_X_base
    {n c : ℕ} (v : BinarySymplecticVector n) (i : Fin n) :
    baseSymplecticEmbedding n c v
        (Fin.castAdd (n + c) (Fin.castAdd c i)) =
      v (Fin.castAdd n i) := by
  simp [baseSymplecticEmbedding, baseSymplecticCoordinate?]

@[simp]
theorem baseSymplecticEmbedding_X_aux
    {n c : ℕ} (v : BinarySymplecticVector n) (i : Fin c) :
    baseSymplecticEmbedding n c v
        (Fin.castAdd (n + c) (Fin.natAdd n i)) = 0 := by
  simp [baseSymplecticEmbedding, baseSymplecticCoordinate?]

@[simp]
theorem baseSymplecticEmbedding_Z_base
    {n c : ℕ} (v : BinarySymplecticVector n) (i : Fin n) :
    baseSymplecticEmbedding n c v
        (Fin.addNat (Fin.castAdd c i) (n + c)) =
      v (Fin.addNat i n) := by
  rw [← Fin.natAdd_eq_addNat (n + c) (Fin.castAdd c i),
    ← Fin.natAdd_eq_addNat n i]
  simp [baseSymplecticEmbedding, baseSymplecticCoordinate?,
    -Fin.natAdd_eq_addNat]

@[simp]
theorem baseSymplecticEmbedding_Z_aux
    {n c : ℕ} (v : BinarySymplecticVector n) (i : Fin c) :
    baseSymplecticEmbedding n c v
        (Fin.addNat (Fin.natAdd n i) (n + c)) = 0 := by
  rw [← Fin.natAdd_eq_addNat (n + c) (Fin.natAdd n i)]
  simp [baseSymplecticEmbedding, baseSymplecticCoordinate?,
    -Fin.natAdd_eq_addNat]

@[simp]
theorem baseSymplecticProjection_X
    {n c : ℕ} (v : BinarySymplecticVector (n + c)) (i : Fin n) :
    baseSymplecticProjection n c v (Fin.castAdd n i) =
      v (Fin.castAdd (n + c) (Fin.castAdd c i)) := by
  simp [baseSymplecticProjection, baseSymplecticCoordinateEmbedding]

@[simp]
theorem baseSymplecticProjection_Z
    {n c : ℕ} (v : BinarySymplecticVector (n + c)) (i : Fin n) :
    baseSymplecticProjection n c v (Fin.addNat i n) =
      v (Fin.addNat (Fin.castAdd c i) (n + c)) := by
  rw [← Fin.natAdd_eq_addNat n i,
    ← Fin.natAdd_eq_addNat (n + c) (Fin.castAdd c i)]
  simp [baseSymplecticProjection, baseSymplecticCoordinateEmbedding,
    -Fin.natAdd_eq_addNat]

@[simp]
theorem auxiliarySymplecticEmbedding_X_base
    {n c : ℕ} (v : BinarySymplecticVector c) (i : Fin n) :
    auxiliarySymplecticEmbedding n c v
        (Fin.castAdd (n + c) (Fin.castAdd c i)) = 0 := by
  simp [auxiliarySymplecticEmbedding, auxiliarySymplecticCoordinate?]

@[simp]
theorem auxiliarySymplecticEmbedding_X_aux
    {n c : ℕ} (v : BinarySymplecticVector c) (i : Fin c) :
    auxiliarySymplecticEmbedding n c v
        (Fin.castAdd (n + c) (Fin.natAdd n i)) =
      v (Fin.castAdd c i) := by
  simp [auxiliarySymplecticEmbedding, auxiliarySymplecticCoordinate?]

@[simp]
theorem auxiliarySymplecticEmbedding_Z_base
    {n c : ℕ} (v : BinarySymplecticVector c) (i : Fin n) :
    auxiliarySymplecticEmbedding n c v
        (Fin.addNat (Fin.castAdd c i) (n + c)) = 0 := by
  rw [← Fin.natAdd_eq_addNat (n + c) (Fin.castAdd c i)]
  simp [auxiliarySymplecticEmbedding, auxiliarySymplecticCoordinate?,
    -Fin.natAdd_eq_addNat]

@[simp]
theorem auxiliarySymplecticEmbedding_Z_aux
    {n c : ℕ} (v : BinarySymplecticVector c) (i : Fin c) :
    auxiliarySymplecticEmbedding n c v
        (Fin.addNat (Fin.natAdd n i) (n + c)) =
      v (Fin.addNat i c) := by
  rw [← Fin.natAdd_eq_addNat (n + c) (Fin.natAdd n i),
    ← Fin.natAdd_eq_addNat c i]
  simp [auxiliarySymplecticEmbedding, auxiliarySymplecticCoordinate?,
    -Fin.natAdd_eq_addNat]

@[simp]
theorem baseSymplecticProjection_apply_auxiliaryEmbedding
    {n c : ℕ} (v : BinarySymplecticVector c) :
    baseSymplecticProjection n c (auxiliarySymplecticEmbedding n c v) = 0 := by
  funext j
  exact Fin.addCases (fun i => by simp) (fun i => by simp) j

theorem auxiliarySymplecticEmbedding_injective (n c : ℕ) :
    Function.Injective (auxiliarySymplecticEmbedding n c) := by
  intro v w h
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have hAt := congrFun h (Fin.castAdd (n + c) (Fin.natAdd n i))
    simpa using hAt
  · have hAt := congrFun h (Fin.natAdd (n + c) (Fin.natAdd n i))
    simpa [Fin.natAdd_eq_addNat] using hAt

@[simp]
theorem baseSymplecticProjection_apply_embedding
    {n c : ℕ} (v : BinarySymplecticVector n) :
    baseSymplecticProjection n c (baseSymplecticEmbedding n c v) = v := by
  funext j
  exact Fin.addCases (fun i => by simp) (fun i => by simp) j

theorem baseSymplecticProjection_comp_embedding (n c : ℕ) :
    (baseSymplecticProjection n c).comp (baseSymplecticEmbedding n c) =
      LinearMap.id := by
  ext v j
  exact Fin.addCases (fun i => by simp) (fun i => by simp) j

theorem baseSymplecticEmbedding_injective (n c : ℕ) :
    Function.Injective (baseSymplecticEmbedding n c) :=
  fun _ _ h => by
    simpa using congrArg (baseSymplecticProjection n c) h

theorem baseSymplecticProjection_surjective (n c : ℕ) :
    Function.Surjective (baseSymplecticProjection n c) :=
  fun v => ⟨baseSymplecticEmbedding n c v, by simp⟩

/- 补零嵌入保持原辛内积，发送端与辅助端之间的辛内积为零。
以下将混合向量的辛内积分解为两端各自的贡献。
-/
theorem symplecticBilinear_embedding_left
    {n c : ℕ} (v : BinarySymplecticVector n)
    (w : BinarySymplecticVector (n + c)) :
    NQubitPauliOperator.symplecticBilinear
        (baseSymplecticEmbedding n c v) w =
      NQubitPauliOperator.symplecticBilinear
        v (baseSymplecticProjection n c w) := by
  simp only [NQubitPauliOperator.symplecticBilinear, Fin.sum_univ_add]
  simp

theorem symplecticBilinear_embedding
    {n c : ℕ} (v w : BinarySymplecticVector n) :
    NQubitPauliOperator.symplecticBilinear
        (baseSymplecticEmbedding n c v)
        (baseSymplecticEmbedding n c w) =
      NQubitPauliOperator.symplecticBilinear v w := by
  rw [symplecticBilinear_embedding_left]
  simp

theorem symplecticBilinear_auxiliaryEmbedding
    {n c : ℕ} (v w : BinarySymplecticVector c) :
    NQubitPauliOperator.symplecticBilinear
        (auxiliarySymplecticEmbedding n c v)
        (auxiliarySymplecticEmbedding n c w) =
      NQubitPauliOperator.symplecticBilinear v w := by
  simp only [NQubitPauliOperator.symplecticBilinear, Fin.sum_univ_add]
  simp

theorem symplecticBilinear_base_auxiliary
    {n c : ℕ} (v : BinarySymplecticVector n)
    (w : BinarySymplecticVector c) :
    NQubitPauliOperator.symplecticBilinear
        (baseSymplecticEmbedding n c v)
        (auxiliarySymplecticEmbedding n c w) = 0 := by
  simp only [NQubitPauliOperator.symplecticBilinear, Fin.sum_univ_add]
  simp

theorem symplecticBilinear_auxiliary_base
    {n c : ℕ} (v : BinarySymplecticVector c)
    (w : BinarySymplecticVector n) :
    NQubitPauliOperator.symplecticBilinear
        (auxiliarySymplecticEmbedding n c v)
        (baseSymplecticEmbedding n c w) = 0 := by
  rw [← binarySymplecticBilinForm_apply,
    (binarySymplecticBilinForm_isSymm (n + c)).eq,
    binarySymplecticBilinForm_apply]
  exact symplecticBilinear_base_auxiliary w v

theorem symplecticBilinear_base_add_auxiliary
    {n c : ℕ} (v w : BinarySymplecticVector n)
    (a b : BinarySymplecticVector c) :
    NQubitPauliOperator.symplecticBilinear
        (baseSymplecticEmbedding n c v + auxiliarySymplecticEmbedding n c a)
        (baseSymplecticEmbedding n c w + auxiliarySymplecticEmbedding n c b) =
      NQubitPauliOperator.symplecticBilinear v w +
        NQubitPauliOperator.symplecticBilinear a b := by
  rw [NQubitPauliOperator.symplecticBilinear_add_left,
    NQubitPauliOperator.symplecticBilinear_add_right,
    NQubitPauliOperator.symplecticBilinear_add_right,
    symplecticBilinear_embedding,
    symplecticBilinear_base_auxiliary,
    symplecticBilinear_auxiliary_base,
    symplecticBilinear_auxiliaryEmbedding]
  simp

namespace BinarySymplecticSubspace

/- 只含 X 坐标的嵌入，用于表示全迷向方向。
-/
private def pureXEmbedding (l : ℕ) :
    (Fin l → ZMod 2) →ₗ[ZMod 2] BinarySymplecticVector l :=
  LinearMap.pi fun j =>
    Fin.addCases
      (fun i : Fin l => LinearMap.proj (R := ZMod 2) i)
      (fun _ : Fin l => 0)
      j

@[simp]
private theorem pureXEmbedding_X {l : ℕ}
    (v : Fin l → ZMod 2) (i : Fin l) :
    pureXEmbedding l v (Fin.castAdd l i) = v i := by
  simp [pureXEmbedding]

@[simp]
private theorem pureXEmbedding_Z {l : ℕ}
    (v : Fin l → ZMod 2) (i : Fin l) :
    pureXEmbedding l v (Fin.natAdd l i) = 0 := by
  simp [pureXEmbedding, -Fin.natAdd_eq_addNat]

private theorem pureXEmbedding_injective (l : ℕ) :
    Function.Injective (pureXEmbedding l) := by
  intro v w h
  funext i
  have hi := congrFun h (Fin.castAdd l i)
  simpa using hi

private theorem symplecticBilinear_pureXEmbedding
    {l : ℕ} (v w : Fin l → ZMod 2) :
    NQubitPauliOperator.symplecticBilinear
      (pureXEmbedding l v) (pureXEmbedding l w) = 0 := by
  simp only [NQubitPauliOperator.symplecticBilinear]
  apply Finset.sum_eq_zero
  intro i _
  simp [pureXEmbedding, -Fin.natAdd_eq_addNat]

/- 指定辛类型的标准模型。用 c 对辛方向及 l 个根空间方向构造子空间，
以下计算其维数、根空间和辛类型。
-/
private abbrev StandardTypeModel (c l : ℕ) :=
  BinarySymplecticVector c × (Fin l → ZMod 2)

private def standardTypeEmbedding (c l r : ℕ) :
    StandardTypeModel c l →ₗ[ZMod 2]
      BinarySymplecticVector ((c + l) + r) :=
  (baseSymplecticEmbedding (c + l) r).comp
    ((baseSymplecticEmbedding c l).comp
        (LinearMap.fst (ZMod 2) (BinarySymplecticVector c)
          (Fin l → ZMod 2)) +
      (auxiliarySymplecticEmbedding c l).comp
        ((pureXEmbedding l).comp
          (LinearMap.snd (ZMod 2) (BinarySymplecticVector c)
            (Fin l → ZMod 2))))

private theorem standardTypeEmbedding_apply
    {c l r : ℕ} (x : BinarySymplecticVector c)
    (a : Fin l → ZMod 2) :
    standardTypeEmbedding c l r (x, a) =
      baseSymplecticEmbedding (c + l) r
        (baseSymplecticEmbedding c l x +
          auxiliarySymplecticEmbedding c l (pureXEmbedding l a)) := by
  rfl

private theorem standardTypeEmbedding_injective (c l r : ℕ) :
    Function.Injective (standardTypeEmbedding c l r) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  rw [standardTypeEmbedding_apply, standardTypeEmbedding_apply] at h
  have hInner := baseSymplecticEmbedding_injective (c + l) r h
  have hBase := congrArg (baseSymplecticProjection c l) hInner
  have hxy : x = y := by simpa using hBase
  subst y
  have hAux :
      auxiliarySymplecticEmbedding c l (pureXEmbedding l a) =
        auxiliarySymplecticEmbedding c l (pureXEmbedding l b) := by
    exact add_left_cancel hInner
  have hpure : pureXEmbedding l a = pureXEmbedding l b :=
    auxiliarySymplecticEmbedding_injective c l hAux
  have hab : a = b := pureXEmbedding_injective l hpure
  subst b
  rfl

private theorem symplecticBilinear_standardTypeEmbedding
    {c l r : ℕ} (u v : StandardTypeModel c l) :
    NQubitPauliOperator.symplecticBilinear
      (standardTypeEmbedding c l r u)
      (standardTypeEmbedding c l r v) =
    NQubitPauliOperator.symplecticBilinear u.1 v.1 := by
  rcases u with ⟨x, a⟩
  rcases v with ⟨y, b⟩
  rw [standardTypeEmbedding_apply, standardTypeEmbedding_apply,
    symplecticBilinear_embedding,
    symplecticBilinear_base_add_auxiliary,
    symplecticBilinear_pureXEmbedding, add_zero]

private def standardTypeSubspace (c l r : ℕ) :
    BinarySymplecticSubspace ((c + l) + r) :=
  LinearMap.range (standardTypeEmbedding c l r)

private def standardTypeRadicalEmbedding (c l r : ℕ) :
    (Fin l → ZMod 2) →ₗ[ZMod 2]
      BinarySymplecticVector ((c + l) + r) :=
  (standardTypeEmbedding c l r).comp
    (LinearMap.inr (ZMod 2) (BinarySymplecticVector c)
      (Fin l → ZMod 2))

private theorem standardTypeRadicalEmbedding_injective (c l r : ℕ) :
    Function.Injective (standardTypeRadicalEmbedding c l r) := by
  apply (standardTypeEmbedding_injective c l r).comp
  exact LinearMap.inr_injective

private theorem radical_standardTypeSubspace (c l r : ℕ) :
    radical (standardTypeSubspace c l r) =
      LinearMap.range (standardTypeRadicalEmbedding c l r) := by
  ext v
  constructor
  · intro hv
    rcases hv.1 with ⟨⟨x, a⟩, rfl⟩
    have hxKernel :
        x ∈ LinearMap.ker (binarySymplecticBilinForm c) := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      have hOrth := hv.2
        (standardTypeEmbedding c l r (y, 0))
        ⟨(y, 0), rfl⟩
      simpa [binarySymplecticBilinForm_apply] using
        (symplecticBilinear_standardTypeEmbedding
          (r := r) (x, a) (y, 0)).symm.trans hOrth
    have hx : x = 0 := by
      rw [(binarySymplecticBilinForm_nondegenerate c).ker_eq_bot] at hxKernel
      simpa using hxKernel
    subst x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    constructor
    · exact ⟨(0, a), rfl⟩
    · intro w hw
      rcases hw with ⟨⟨y, b⟩, rfl⟩
      rw [show standardTypeRadicalEmbedding c l r a =
        standardTypeEmbedding c l r (0, a) from rfl,
        symplecticBilinear_standardTypeEmbedding]
      simp [NQubitPauliOperator.symplecticBilinear]

private theorem standardTypeSubspace_finrank (c l r : ℕ) :
    Module.finrank (ZMod 2) (standardTypeSubspace c l r) = 2 * c + l := by
  rw [standardTypeSubspace,
    LinearMap.finrank_range_of_inj (standardTypeEmbedding_injective c l r),
    Module.finrank_prod]
  simp [BinarySymplecticVector]
  omega

private theorem standardTypeSubspace_radical_finrank (c l r : ℕ) :
    Module.finrank (ZMod 2) (radical (standardTypeSubspace c l r)) = l := by
  rw [radical_standardTypeSubspace,
    LinearMap.finrank_range_of_inj
      (standardTypeRadicalEmbedding_injective c l r)]
  simp

private theorem standardTypeSubspace_hasType (c l r : ℕ) :
    (standardTypeSubspace c l r).HasType (2 * c + l) c := by
  refine ⟨standardTypeSubspace_finrank c l r, ?_⟩
  have hRankNullity :=
    (standardTypeSubspace c l r).symplecticRank_add_radicalFinrank_eq_finrank
  rw [standardTypeSubspace_radical_finrank,
    standardTypeSubspace_finrank] at hRankNullity
  omega

/-- 辛类型的存在条件。存在类型 [m,c]ₛ 的子空间，当且仅当 2c ≤ m 且 m ≤ n + c。
-/
theorem exists_hasType_iff {n m c : ℕ} :
    (∃ S : BinarySymplecticSubspace n, S.HasType m c) ↔
      2 * c ≤ m ∧ m ≤ n + c := by
  constructor
  · rintro ⟨S, hType⟩
    constructor
    · have hRadical := radicalFinrank_add_two_mul_eq_of_hasType hType
      omega
    · exact dimension_le_length_add_typeParameter_of_hasType hType
  · rintro ⟨hLower, hUpper⟩
    let l := m - 2 * c
    have hDimension : 2 * c + l = m := by
      dsimp [l]
      omega
    have hCoordinateBound : c + l ≤ n := by
      dsimp [l]
      omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hCoordinateBound
    refine ⟨standardTypeSubspace c l r, ?_⟩
    simpa [hDimension] using standardTypeSubspace_hasType c l r

/- 扩展子空间的两种发送端空间：删除辅助坐标所得的投影，
以及辅助坐标全部为零时对应的发送端向量。以下给出两者的成员判定。
-/
def projectedSpace {n c : ℕ}
    (T : BinarySymplecticSubspace (n + c)) :
    BinarySymplecticSubspace n :=
  T.map (baseSymplecticProjection n c)

def baseOnlySpace {n c : ℕ}
    (T : BinarySymplecticSubspace (n + c)) :
    BinarySymplecticSubspace n :=
  T.comap (baseSymplecticEmbedding n c)

@[simp]
theorem mem_baseOnlySpace_iff
    {n c : ℕ} (T : BinarySymplecticSubspace (n + c))
    (v : BinarySymplecticVector n) :
    v ∈ T.baseOnlySpace ↔ baseSymplecticEmbedding n c v ∈ T := by
  rfl

theorem mem_projectedSpace_iff
    {n c : ℕ} (T : BinarySymplecticSubspace (n + c))
    (v : BinarySymplecticVector n) :
    v ∈ T.projectedSpace ↔
      ∃ w, w ∈ T ∧ baseSymplecticProjection n c w = v := by
  rfl

end BinarySymplecticSubspace

/-- 扩展子空间实现输入辛子空间的条件。扩展空间须全迷向，发送端投影在其上单射，
投影像为 S，且辅助坐标为零的部分恰为 S 的辛根空间。
-/
def RealizesEAStabilizerSpace
    {n c : ℕ} (T : BinarySymplecticSubspace (n + c))
    (S : BinarySymplecticSubspace n) : Prop :=
  T.IsTotallyIsotropic ∧
    T ⊓ LinearMap.ker (baseSymplecticProjection n c) = ⊥ ∧
    T.projectedSpace = S ∧
    T.baseOnlySpace = symplecticRadical S

theorem RealizesEAStabilizerSpace.baseEmbedding_mem_sympOrthogonal_iff
    {n c : ℕ} {T : BinarySymplecticSubspace (n + c)}
    {S : BinarySymplecticSubspace n}
    (hRealizes : RealizesEAStabilizerSpace T S)
    (v : BinarySymplecticVector n) :
    baseSymplecticEmbedding n c v ∈
        NQubitPauliGroupElement.sympOrthogonal T ↔
      v ∈ NQubitPauliGroupElement.sympOrthogonal S := by
  have hProjected : T.projectedSpace = S := hRealizes.2.2.1
  constructor
  · intro hv s hs
    have hsProjected : s ∈ T.projectedSpace := by
      rw [hProjected]
      exact hs
    rcases (BinarySymplecticSubspace.mem_projectedSpace_iff T s).mp
      hsProjected with ⟨t, ht, hProjection⟩
    have htOrthogonal := hv t ht
    rw [symplecticBilinear_embedding_left, hProjection] at htOrthogonal
    exact htOrthogonal
  · intro hv t ht
    rw [symplecticBilinear_embedding_left]
    apply hv
    rw [← hProjected]
    exact (BinarySymplecticSubspace.mem_projectedSpace_iff T
      (baseSymplecticProjection n c t)).mpr ⟨t, ht, rfl⟩

end Quantum

namespace Quantum
namespace BinarySymplecticSubspace
namespace RadicalDecomposition

/- 取输入向量在非退化补空间上的分量，再映射到标准辛坐标以构造辅助修正。
-/
noncomputable def nondegenerateProjection
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) :
    S →ₗ[ZMod 2] D.nondegeneratePart :=
  (Submodule.comapSubtypeEquivOfLe D.nondegeneratePart_le).toLinearMap.comp
    (D.nondegeneratePartWithin.linearProjOfIsCompl
      D.radicalWithin
      D.radicalWithin_isCompl_nondegeneratePartWithin.symm)

theorem nondegenerateProjection_apply_eq_zero_iff
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (s : S) :
    D.nondegenerateProjection s = 0 ↔ (s : BinarySymplecticVector n) ∈ radical S := by
  change (Submodule.comapSubtypeEquivOfLe D.nondegeneratePart_le)
      ((D.nondegeneratePartWithin.linearProjOfIsCompl
        D.radicalWithin
        D.radicalWithin_isCompl_nondegeneratePartWithin.symm) s) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  change (D.nondegeneratePartWithin.linearProjOfIsCompl
      D.radicalWithin
      D.radicalWithin_isCompl_nondegeneratePartWithin.symm) s = 0 ↔
    s ∈ D.radicalWithin
  exact Submodule.linearProjOfIsCompl_apply_eq_zero_iff
    D.radicalWithin_isCompl_nondegeneratePartWithin.symm

theorem coe_nondegenerateProjection
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (s : S) :
    ((D.nondegenerateProjection s : D.nondegeneratePart) :
        BinarySymplecticVector n) =
      (((Submodule.IsCompl.projection
          D.radicalWithin_isCompl_nondegeneratePartWithin.symm s) : S) :
        BinarySymplecticVector n) := by
  rfl

theorem symplecticBilinear_nondegenerateProjection
    {n : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (s t : S) :
    NQubitPauliOperator.symplecticBilinear
        (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) =
      NQubitPauliOperator.symplecticBilinear
        (D.nondegenerateProjection s : BinarySymplecticVector n)
        (D.nondegenerateProjection t : BinarySymplecticVector n) := by
  let hCompl : IsCompl D.nondegeneratePartWithin D.radicalWithin :=
    D.radicalWithin_isCompl_nondegeneratePartWithin.symm
  let ps : S := Submodule.IsCompl.projection hCompl s
  let rs : S := Submodule.IsCompl.projection hCompl.symm s
  let pt : S := Submodule.IsCompl.projection hCompl t
  let rt : S := Submodule.IsCompl.projection hCompl.symm t
  have hsDecomposition : ps + rs = s := by
    exact Submodule.IsCompl.projection_add_projection_eq_self hCompl s
  have htDecomposition : pt + rt = t := by
    exact Submodule.IsCompl.projection_add_projection_eq_self hCompl t
  have hrsRadical : (rs : BinarySymplecticVector n) ∈ radical S := by
    exact Submodule.IsCompl.projection_apply_mem hCompl.symm s
  have hrtRadical : (rt : BinarySymplecticVector n) ∈ radical S := by
    exact Submodule.IsCompl.projection_apply_mem hCompl.symm t
  have hrsOrthogonalT :
      NQubitPauliOperator.symplecticBilinear
          (rs : BinarySymplecticVector n) (t : BinarySymplecticVector n) = 0 :=
    hrsRadical.2 t t.2
  have hpsOrthogonalRt :
      NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n) (rt : BinarySymplecticVector n) = 0 := by
    rw [← binarySymplecticBilinForm_apply,
      (binarySymplecticBilinForm_isSymm n).eq,
      binarySymplecticBilinForm_apply]
    exact hrtRadical.2 ps ps.2
  rw [D.coe_nondegenerateProjection s, D.coe_nondegenerateProjection t]
  change NQubitPauliOperator.symplecticBilinear
      (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) =
    NQubitPauliOperator.symplecticBilinear
      (ps : BinarySymplecticVector n) (pt : BinarySymplecticVector n)
  calc
    NQubitPauliOperator.symplecticBilinear
        (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) =
      NQubitPauliOperator.symplecticBilinear
        ((ps + rs : S) : BinarySymplecticVector n)
        (t : BinarySymplecticVector n) := by rw [hsDecomposition]
    _ = NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n) (t : BinarySymplecticVector n) +
        NQubitPauliOperator.symplecticBilinear
          (rs : BinarySymplecticVector n) (t : BinarySymplecticVector n) := by
      exact NQubitPauliOperator.symplecticBilinear_add_left _ _ _
    _ = NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n) (t : BinarySymplecticVector n) := by
      rw [hrsOrthogonalT, add_zero]
    _ = NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n)
          ((pt + rt : S) : BinarySymplecticVector n) := by rw [htDecomposition]
    _ = NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n) (pt : BinarySymplecticVector n) +
        NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n) (rt : BinarySymplecticVector n) := by
      exact NQubitPauliOperator.symplecticBilinear_add_right _ _ _
    _ = NQubitPauliOperator.symplecticBilinear
          (ps : BinarySymplecticVector n) (pt : BinarySymplecticVector n) := by
      rw [hpsOrthogonalRt, add_zero]

noncomputable def auxiliaryCorrection
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    S →ₗ[ZMod 2] BinarySymplecticVector c :=
  (D.entanglementPairBasis hType).toStandardCoordinates.toLinearMap.comp
    D.nondegenerateProjection

theorem symplecticBilinear_auxiliaryCorrection
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c)
    (s t : S) :
    NQubitPauliOperator.symplecticBilinear
        (D.auxiliaryCorrection hType s) (D.auxiliaryCorrection hType t) =
      NQubitPauliOperator.symplecticBilinear
        (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) := by
  let P := D.entanglementPairBasis hType
  have hSymm :
      ((binarySymplecticBilinForm n).restrict D.nondegeneratePart).IsSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    exact (binarySymplecticBilinForm_isSymm n).eq v w
  have hCoordinates := P.symplecticBilinear_toStandardCoordinates hSymm
    (D.nondegenerateProjection s) (D.nondegenerateProjection t)
  change NQubitPauliOperator.symplecticBilinear
      (D.auxiliaryCorrection hType s) (D.auxiliaryCorrection hType t) = _
  calc
    NQubitPauliOperator.symplecticBilinear
        (D.auxiliaryCorrection hType s) (D.auxiliaryCorrection hType t) =
      ((binarySymplecticBilinForm n).restrict D.nondegeneratePart)
        (D.nondegenerateProjection s) (D.nondegenerateProjection t) := by
      exact hCoordinates
    _ = NQubitPauliOperator.symplecticBilinear
        (D.nondegenerateProjection s : BinarySymplecticVector n)
        (D.nondegenerateProjection t : BinarySymplecticVector n) := rfl
    _ = NQubitPauliOperator.symplecticBilinear
        (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) :=
      D.symplecticBilinear_nondegenerateProjection s t |>.symm

theorem auxiliaryCorrection_apply_eq_zero_iff
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c)
    (s : S) :
    D.auxiliaryCorrection hType s = 0 ↔
      (s : BinarySymplecticVector n) ∈ radical S := by
  change (D.entanglementPairBasis hType).toStandardCoordinates
      (D.nondegenerateProjection s) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact D.nondegenerateProjection_apply_eq_zero_iff s

/-- 辅助扩展映射。把发送端向量与其非退化部分的辅助修正相加，
使发送端和辅助端的辛内积相互抵消，同时保持发送端投影不变。
-/
noncomputable def eaExtensionMap
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    S →ₗ[ZMod 2] BinarySymplecticVector (n + c) :=
  (baseSymplecticEmbedding n c).comp S.subtype +
    (auxiliarySymplecticEmbedding n c).comp
      (D.auxiliaryCorrection hType)

@[simp]
theorem baseSymplecticProjection_apply_eaExtensionMap
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c)
    (s : S) :
    baseSymplecticProjection n c (D.eaExtensionMap hType s) = s := by
  simp [eaExtensionMap]

theorem eaExtensionMap_injective
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    Function.Injective (D.eaExtensionMap hType) := by
  intro s t h
  have hProjected := congrArg (baseSymplecticProjection n c) h
  simpa using hProjected

theorem symplecticBilinear_eaExtensionMap
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c)
    (s t : S) :
    NQubitPauliOperator.symplecticBilinear
        (D.eaExtensionMap hType s) (D.eaExtensionMap hType t) = 0 := by
  rw [eaExtensionMap, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    symplecticBilinear_base_add_auxiliary,
    D.symplecticBilinear_auxiliaryCorrection hType s t]
  have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  calc
    NQubitPauliOperator.symplecticBilinear
          (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) +
        NQubitPauliOperator.symplecticBilinear
          (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) =
      2 * NQubitPauliOperator.symplecticBilinear
          (s : BinarySymplecticVector n) (t : BinarySymplecticVector n) := by ring
    _ = 0 := by rw [htwo, zero_mul]

/- 扩展映射的像。以下证明其维数、全迷向性、投影恢复及根空间恢复关系，
由此得到满足上述实现条件的扩展子空间。
-/
noncomputable def extendedStabilizerSpace
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    BinarySymplecticSubspace (n + c) :=
  LinearMap.range (D.eaExtensionMap hType)

theorem extendedStabilizerSpace_finrank
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    Module.finrank (ZMod 2) (D.extendedStabilizerSpace hType) = m := by
  have hEquiv := LinearEquiv.ofInjective
    (D.eaExtensionMap hType) (D.eaExtensionMap_injective hType)
  calc
    Module.finrank (ZMod 2) (D.extendedStabilizerSpace hType) =
        Module.finrank (ZMod 2) S := hEquiv.finrank_eq.symm
    _ = m := hType.1

theorem extendedStabilizerSpace_isTotallyIsotropic
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    (D.extendedStabilizerSpace hType).IsTotallyIsotropic := by
  intro x hx y hy
  rcases hx with ⟨s, rfl⟩
  rcases hy with ⟨t, rfl⟩
  exact D.symplecticBilinear_eaExtensionMap hType s t

theorem extendedStabilizerSpace_inf_projectionKer_eq_bot
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    D.extendedStabilizerSpace hType ⊓
        LinearMap.ker (baseSymplecticProjection n c) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases hx.1 with ⟨s, rfl⟩
  have hsCoe : (s : BinarySymplecticVector n) = 0 := by
    have hProjection := LinearMap.mem_ker.mp hx.2
    simpa using hProjection
  have hs : s = 0 := Subtype.ext hsCoe
  rw [hs]
  simp

theorem extendedStabilizerSpace_projectedSpace_eq
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    (D.extendedStabilizerSpace hType).projectedSpace = S := by
  ext v
  constructor
  · intro hv
    rcases (mem_projectedSpace_iff
      (D.extendedStabilizerSpace hType) v).mp hv with ⟨w, hw, hProjection⟩
    rcases hw with ⟨s, rfl⟩
    rw [D.baseSymplecticProjection_apply_eaExtensionMap hType] at hProjection
    rw [← hProjection]
    exact s.2
  · intro hv
    apply (mem_projectedSpace_iff
      (D.extendedStabilizerSpace hType) v).mpr
    let s : S := ⟨v, hv⟩
    refine ⟨D.eaExtensionMap hType s, ⟨s, rfl⟩, ?_⟩
    exact D.baseSymplecticProjection_apply_eaExtensionMap hType s

theorem extendedStabilizerSpace_baseOnlySpace_eq_radical
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    (D.extendedStabilizerSpace hType).baseOnlySpace = radical S := by
  ext v
  constructor
  · intro hv
    rw [mem_baseOnlySpace_iff] at hv
    rcases hv with ⟨s, hExtension⟩
    have hsCoe : (s : BinarySymplecticVector n) = v := by
      have hProjected := congrArg (baseSymplecticProjection n c) hExtension
      simpa using hProjected
    have hAuxiliary :
        auxiliarySymplecticEmbedding n c
          (D.auxiliaryCorrection hType s) = 0 := by
      have hExtension' :
          baseSymplecticEmbedding n c (s : BinarySymplecticVector n) +
              auxiliarySymplecticEmbedding n c
                (D.auxiliaryCorrection hType s) =
            baseSymplecticEmbedding n c (s : BinarySymplecticVector n) := by
        simpa [eaExtensionMap, hsCoe] using hExtension
      exact (add_eq_left.mp hExtension')
    have hCorrection : D.auxiliaryCorrection hType s = 0 := by
      apply auxiliarySymplecticEmbedding_injective n c
      simpa using hAuxiliary
    have hsRadical :=
      (D.auxiliaryCorrection_apply_eq_zero_iff hType s).mp hCorrection
    simpa [hsCoe] using hsRadical
  · intro hv
    rw [mem_baseOnlySpace_iff]
    let s : S := ⟨v, hv.1⟩
    have hCorrection : D.auxiliaryCorrection hType s = 0 :=
      (D.auxiliaryCorrection_apply_eq_zero_iff hType s).mpr hv
    refine ⟨s, ?_⟩
    simp [eaExtensionMap, hCorrection, s]

theorem extendedStabilizerSpace_realizesEAStabilizerSpace
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (D : RadicalDecomposition S) (hType : S.HasType m c) :
    RealizesEAStabilizerSpace (D.extendedStabilizerSpace hType) S := by
  exact ⟨D.extendedStabilizerSpace_isTotallyIsotropic hType,
    D.extendedStabilizerSpace_inf_projectionKer_eq_bot hType,
    D.extendedStabilizerSpace_projectedSpace_eq hType,
    D.extendedStabilizerSpace_baseOnlySpace_eq_radical hType⟩

end RadicalDecomposition

theorem exists_realizingEAStabilizerSpace_of_hasType
    {n m c : ℕ} {S : BinarySymplecticSubspace n}
    (hType : S.HasType m c) :
    ∃ T : BinarySymplecticSubspace (n + c),
      RealizesEAStabilizerSpace T S := by
  let D := radicalDecomposition S
  exact ⟨D.extendedStabilizerSpace hType,
    D.extendedStabilizerSpace_realizesEAStabilizerSpace hType⟩

end BinarySymplecticSubspace

namespace EASymplecticData

theorem exists_realizingEAStabilizerSpace
    {n m l c k : ℕ} (A : EASymplecticData n m l c k) :
    ∃ T : BinarySymplecticSubspace (n + c),
      RealizesEAStabilizerSpace T A.stabilizerSpace :=
  BinarySymplecticSubspace.exists_realizingEAStabilizerSpace_of_hasType
    A.hasType

end EASymplecticData
end Quantum
