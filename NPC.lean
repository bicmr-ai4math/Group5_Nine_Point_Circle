/-
Authors (listed in no particular order): Ruiheng Mao, Huanyu Zheng, Aiwei Liu, Yinuo Zhang, Jiayang Dong
-/


import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

/-我们小组的最初目标是将九点圆的证明写成lean的代码,不过我们现在更多地是完成了九点圆证明的各种前置内容,
  目前我们已经完成了如下内容:
  1.非退化三角形垂心的定义与相关性质;
  2.非退化线段中垂线的定义与相关性质(有一部分sorry,原因是lean中三角形全等的情况十分复杂);
  3.非退化三角形外心与外接圆的定义及性质;
  4.证明了非退化三角形外心、垂心、九点圆圆心在顶点轮换下保持不变(类似可以证明顶点置换也保持不变);
  5.证明了直角三角形的部分性质;
  6.需要等腰三角形相关性质,但没有时间写;
  7.九点圆的证明:先证明一半中点、一条高的垂足和垂心与一个顶点连线的中点在九点圆上(基本上全是sorry);
    最后利用九点圆圆心在顶点轮换下保持不变的性质完成证明.
  我们遇到的困难有(这也是我们写sorry的原因):
  1.lean的语言十分严格,很多自然语言一笔带过的证明在lean中都得花十多行写出来;
  2.三角形全等与相似十分复杂,lean中的全等与相似需要考虑三角形顶点的排列(顺时针与逆时针),导致证明十分困难;
  3.平面几何退化情况过多,处理起来麻烦,两点重合与多点共线的退化情况不能享用非退化时的证明,需要额外进行分类谈论;
  4.位置关系复杂(没有“如图”),其一是情况繁多,例如垂心就能够位于三角形内、与顶点重合、位于三角形外;
    其二是讨论与证明复杂,例如垂心的三种情况还没有得到证明,又如多点共线时线段的长度关系甚至都不容易计算.
  5.各种性质转换复杂,例如垂直、形成直角与内积为零,这些自然语言中能一步到位的情况,在lean中可能得花上不少篇幅.
-/

--我们用三角形ABC来表示非退化三角形tr,其中A、B、C分别为点tr.1.1、tr.1.2、tr.1.3

--我们遇到了两种中点的定义方法,我们证明其等价,以便在后面的证明中同时调用两边的相关结论.
lemma MID (A B : P) : midpoint ℝ A B = (SEG A B).midpoint := by
  dsimp [midpoint, Seg.midpoint]
  field_simp
  rfl

--两点连线的方向与两点构成向量的方向相同.
lemma Proj_eq_for_line_and_vec (A B : P) (h : B ≠ A) : toProj (Line.mk_pt_pt A B h) = (VEC_nd A B h) := by rfl

--证明AB与CA所在直线不平行.
lemma Not_Para_if_nd (tr : TriangleND P) :
    ¬ Line.mk_pt_pt tr.1.1 tr.1.2  (ne_of_not_collinear tr.2).2.2 ∥ Line.mk_pt_pt tr.1.3 tr.1.1  (ne_of_not_collinear tr.2).2.1 := by
  let AB := Line.mk_pt_pt tr.1.1 tr.1.2  (ne_of_not_collinear tr.2).2.2
  let CA := Line.mk_pt_pt tr.1.3 tr.1.1  (ne_of_not_collinear tr.2).2.1
  show ¬ toProj AB = toProj CA
  by_contra h1
  have h2 : ¬ Collinear tr.1.1 tr.1.2 tr.1.3 := tr.2
  have h3 := ne_of_not_collinear h2
  have h4 : ¬ ((tr.1.3 = tr.1.2) ∨ (tr.1.1 = tr.1.3) ∨ (tr.1.2 = tr.1.1)) := by tauto
  contrapose! h2
  dsimp [Collinear]
  rw [dif_neg h4]
  dsimp [collinear_of_nd]
  have hab : toProj AB = (VEC_nd tr.1.1 tr.1.2 h3.2.2).toProj := Proj_eq_for_line_and_vec tr.1.1 tr.1.2 h3.2.2
  have hca : toProj CA = (VEC_nd tr.1.3 tr.1.1 h3.2.1).toProj := Proj_eq_for_line_and_vec tr.1.3 tr.1.1 h3.2.1
  have : (VEC_nd tr.1.1 tr.1.3 h3.2.1.symm).toProj = (VEC_nd tr.1.3 tr.1.1 h3.2.1).toProj := by
    rw [VecND.toProj_eq_toProj_iff₀]
    use -1
    rw [← VecND.neg_vecND, RayVector.coe_neg]
    simp
  rw [hab, hca, ← this] at h1
  exact h1

--定义三条高所在直线
def Height_Line₁ (tr : TriangleND P) : Line P :=
  perp_line tr.1.1 (Line.mk_pt_pt tr.1.2 tr.1.3  (ne_of_not_collinear tr.2).1)

def Height_Line₂ (tr : TriangleND P) : Line P :=
  perp_line tr.1.2 (Line.mk_pt_pt tr.1.3 tr.1.1  (ne_of_not_collinear tr.2).2.1)

def Height_Line₃ (tr : TriangleND P) : Line P :=
  perp_line tr.1.3 (Line.mk_pt_pt tr.1.1 tr.1.2  (ne_of_not_collinear tr.2).2.2)

--定义:垂心H为满足H与顶点连线与对边垂直的点,采用向量内积定义.
structure Is_Orthocenter (tr : TriangleND P) (H : P) : Prop where
  perp1 : inner (VEC tr.1.1 H) (VEC tr.1.2 tr.1.3) = (0 : ℝ)
  perp2 : inner (VEC tr.1.2 H) (VEC tr.1.3 tr.1.1) = (0 : ℝ)
  perp3 : inner (VEC tr.1.3 H) (VEC tr.1.1 tr.1.2) = (0 : ℝ)

--证明点H只需满足上述定义的其中两条就能推出H是垂心.
theorem orthocenter_exists (tr : TriangleND P) (H : P)
  (h₁ : inner (VEC tr.point₁ H) (VEC tr.point₂ tr.point₃) = (0 : ℝ))
  (h₂ : inner (VEC tr.point₂ H) (VEC tr.point₃ tr.point₁) = (0 : ℝ))
  : inner (VEC tr.point₃ H) (VEC tr.point₁ tr.point₂) = (0 : ℝ) := by
  set A := tr.point₁
  set B := tr.point₂
  set C := tr.point₃
  rw [← vec_sub_vec C, inner_sub_left, sub_eq_zero] at h₁ h₂
  rw [← vec_sub_vec C A B, inner_sub_right, sub_eq_zero, ← neg_vec B C, inner_neg_right, h₁, h₂, real_inner_comm, ← inner_neg_left, neg_vec]

lemma two_perp_not_para (l₁ l₂ l₃ l₄ : Line P) (h₁ : ¬ (l₁ ∥ l₂)) (h₂ : l₃ ⟂ l₁) (h₃ : l₄ ⟂ l₂) : ¬ (l₃ ∥ l₄) := by
  by_contra h
  have := h₂.symm
  have := perp_of_perp_parallel this h
  have := parallel_of_perp_perp this h₃
  contradiction

--证明两条高不平行.
lemma Height₁₂_not_para (tr : TriangleND P) : ¬(Height_Line₁ tr ∥ Height_Line₂ tr) := by
  apply two_perp_not_para (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm)
  · have : (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) = (LIN tr.1.3 tr.1.2  (ne_of_not_collinear tr.2).1.symm) := by apply Line.line_of_pt_pt_eq_rev
    rw[this]
    apply Not_Para_if_nd (tr.flip_vertices.perm_vertices)
  · apply perp_line_perp tr.1.1
  · have : (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) = (LIN tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) := Line.line_of_pt_pt_eq_rev
    rw[this]
    apply perp_line_perp tr.1.2

--构造垂心:为三角形两条高的交点.
def Orthocenter (tr : TriangleND P) : P :=
  --定义为两条边上高的交点
  Line.inx (Height_Line₁ tr) (Height_Line₂ tr) (Height₁₂_not_para tr)

--接下来证明我们构造的点确实是垂心,下面是一些辅助引理.
lemma aux_inter_is_Orthocenter (tr : TriangleND P) : ⟪VEC tr.1.1 (Orthocenter tr), VEC tr.1.2 tr.1.3⟫_ℝ = 0 := by
  have ocenter_lies_on_h1: Orthocenter tr LiesOn Height_Line₁ tr := Line.inx_lies_on_fst (Height₁₂_not_para tr)
  have tr1_lieson_h1 : tr.1.1 LiesOn Height_Line₁ tr := by
    unfold Height_Line₁ perp_line --这个unfold不能删
    apply Line.pt_lies_on_of_mk_pt_proj
  by_cases eq : Orthocenter tr = tr.1.1
  · rw [eq, (eq_iff_vec_eq_zero (tr.1.1) (tr.1.1)).1, inner_zero_left]; rfl
  · have : (VEC_nd tr.1.1 (Orthocenter tr) eq) ⟂ (VEC_nd tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := by
      have : PtNe tr.1.1 (Orthocenter tr) := by push_neg at eq; exact { out := id (Ne.symm eq) } -- 不能删，后面Line.snd_pt_lies_on_mk_pt_pt会报错
      have ocenter_lies_on_l1 : Orthocenter tr LiesOn (LIN tr.1.1 (Orthocenter tr) eq) := Line.snd_pt_lies_on_mk_pt_pt
      have tr1_lieson_l1 : tr.1.1 LiesOn (LIN tr.1.1 (Orthocenter tr) eq) := Line.fst_pt_lies_on_mk_pt_pt
      have line_eq_height : (LIN tr.1.1 (Orthocenter tr) eq) = (Height_Line₁ tr) := (Line.eq_of_pt_pt_lies_on_of_ne (tr1_lieson_h1) (ocenter_lies_on_h1) (tr1_lieson_l1) (ocenter_lies_on_l1)).symm
        -- ↑上面都是废话，但是不知道为什么不能删（
      have vec1_eq_line1: (VEC_nd tr.1.1 (Orthocenter tr) eq) = toProj (Height_Line₁ tr) := by
        rw [← Proj_eq_for_line_and_vec tr.1.1 (Orthocenter tr) eq, line_eq_height]
      rw [VecND.toDir_toProj] at vec1_eq_line1
      exact vec1_eq_line1
    apply (inner_product_eq_zero_of_perp (VEC_nd tr.1.1 (Orthocenter tr) eq) (VEC_nd tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) this)

lemma aux_inter_is_Orthocenter_perm (tr : TriangleND P) : ⟪VEC tr.1.2 (Orthocenter tr), VEC tr.1.3 tr.1.1⟫_ℝ = 0 := by
  have ocenter_lies_on_h2: Orthocenter tr LiesOn Height_Line₂ tr := Line.inx_lies_on_snd (Height₁₂_not_para tr)
  have tr2_lieson_h2 : tr.1.2 LiesOn Height_Line₂ tr := by
    unfold Height_Line₂ perp_line --这个unfold不能删
    apply Line.pt_lies_on_of_mk_pt_proj
  by_cases eq : Orthocenter tr = tr.1.2
  · rw [eq, (eq_iff_vec_eq_zero (tr.1.2) (tr.1.2)).1, inner_zero_left]; rfl
  · have : (VEC_nd tr.1.2 (Orthocenter tr) eq) ⟂ (VEC_nd tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) := by
      have : PtNe tr.1.2 (Orthocenter tr) := by push_neg at eq; exact { out := id (Ne.symm eq) }
      have ocenter_lies_on_l2 : Orthocenter tr LiesOn (LIN tr.1.2 (Orthocenter tr) eq) := Line.snd_pt_lies_on_mk_pt_pt
      have tr2_lieson_l2 : tr.1.2 LiesOn (LIN tr.1.2 (Orthocenter tr) eq) := Line.fst_pt_lies_on_mk_pt_pt
      have line_eq_height : (LIN tr.1.2 (Orthocenter tr) eq) = (Height_Line₂ tr) := (Line.eq_of_pt_pt_lies_on_of_ne (tr2_lieson_h2) (ocenter_lies_on_h2) (tr2_lieson_l2) (ocenter_lies_on_l2)).symm
      have vec2_eq_line2: (VEC_nd tr.1.2 (Orthocenter tr) eq) = toProj (Height_Line₂ tr) := by
        rw [← Proj_eq_for_line_and_vec tr.1.2 (Orthocenter tr) eq, line_eq_height]
      rw [VecND.toDir_toProj] at vec2_eq_line2
      exact vec2_eq_line2
    apply (inner_product_eq_zero_of_perp (VEC_nd tr.1.2 (Orthocenter tr) eq) (VEC_nd tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) this)

--证明我们构造的点确实是垂心.
theorem Orthocenter_is_Orthocenter (tr : TriangleND P) : Is_Orthocenter tr (Orthocenter tr) := by
  constructor
  . exact aux_inter_is_Orthocenter tr
  · exact aux_inter_is_Orthocenter_perm tr
  · by_cases eq : Orthocenter tr = tr.1.3
    · rw [eq, (eq_iff_vec_eq_zero (tr.1.3) (tr.1.3)).1, inner_zero_left]; rfl
    · apply orthocenter_exists tr (Orthocenter tr) (aux_inter_is_Orthocenter tr)
      exact aux_inter_is_Orthocenter_perm tr

--证明我们构造的垂心位于三条高所在直线上.
theorem Orthocenter_on_height (tr : TriangleND P) : Orthocenter tr LiesOn (Height_Line₁ tr) := Line.inx_lies_on_fst (Height₁₂_not_para tr)

theorem Orthocenter_on_height' (tr : TriangleND P) : Orthocenter tr LiesOn (Height_Line₂ tr) := Line.inx_lies_on_snd (Height₁₂_not_para tr)

lemma aux_Orthocenter_on_height'' (p₁ p₂ : P) (l₁ : Line P) (nd : p₁ ≠ p₂) (vert : (LIN p₁ p₂ nd.symm) ⟂ l₁) : p₂ LiesOn perp_line p₁ l₁ := by
  unfold perp_line
  have : l₁.toProj.perp = (toProj l₁).perp := rfl
  rw [this, ← vert]
  have : Line.mk_pt_proj p₁ (toProj (LIN p₁ p₂ nd.symm)) = LIN p₁ p₂ nd.symm := rfl
  rw [this]
  have : PtNe p₂ p₁ := by exact { out := id (Ne.symm nd) }
  apply Line.snd_pt_lies_on_mk_pt_pt

theorem Orthocenter_on_height'' (tr : TriangleND P) : Orthocenter tr LiesOn (Height_Line₃ tr) := by
  have : ⟪(VEC tr.1.3 (Orthocenter tr)), (VEC tr.1.1 tr.1.2)⟫_ℝ = 0 := (Orthocenter_is_Orthocenter tr).3
  by_cases eq : Orthocenter tr = tr.1.3
  · rw [eq]
    unfold Height_Line₃ perp_line
    apply Line.pt_lies_on_of_mk_pt_proj
  · have : (LIN tr.1.3 (Orthocenter tr) eq) ⟂ (LIN tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) := perp_of_inner_product_eq_zero (VEC_nd tr.1.3 (Orthocenter tr) eq) (VEC_nd tr.1.1 tr.1.2) this
    unfold Height_Line₃
    apply aux_Orthocenter_on_height'' tr.1.3 (Orthocenter tr) (LIN tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) (Ne.symm eq) this

--证明垂心的唯一性,点与我们构造的垂心重合当且仅当其满足垂心的三条性质.
theorem Orthocenter_iff_Is_Orthocenter (tr : TriangleND P) (H : P) : Is_Orthocenter tr H ↔ H = Orthocenter tr := by
  constructor
  · intro h
    have h1 : H LiesOn Height_Line₁ tr := by
      by_cases eq : H = tr.1.1
      · rw [eq]
        unfold Height_Line₁ perp_line
        apply Line.pt_lies_on_of_mk_pt_proj
      · have : (LIN tr.1.1 H eq) ⟂ (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := perp_of_inner_product_eq_zero (VEC_nd tr.1.1 H eq) (VEC_nd tr.1.2 tr.1.3) h.1
        unfold Height_Line₁
        apply aux_Orthocenter_on_height'' tr.1.1 H (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) (Ne.symm eq) this
    have h2 : H LiesOn Height_Line₂ tr := by
      by_cases eq : H = tr.1.2
      · rw [eq]
        unfold Height_Line₂ perp_line
        apply Line.pt_lies_on_of_mk_pt_proj
      · have : (LIN tr.1.2 H eq) ⟂ (LIN tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) := perp_of_inner_product_eq_zero (VEC_nd tr.1.2 H eq) (VEC_nd tr.1.3 tr.1.1) h.2
        unfold Height_Line₂
        apply aux_Orthocenter_on_height'' tr.1.2 H (LIN tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) (Ne.symm eq) this
    have := exists_unique_intersection_of_nonparallel_lines (Height₁₂_not_para tr)
    rcases this with ⟨p, _, h'⟩
    have h'1 := h' H ⟨h1, h2⟩
    have h'2 := h' (Orthocenter tr) ⟨Orthocenter_on_height tr, Orthocenter_on_height' tr⟩
    rw [h'1]
    exact h'2.symm
  · intro h
    rw [h]
    exact Orthocenter_is_Orthocenter tr

--定义中垂线为满足到线段两端点距离相等的点的集合.
structure Is_PerpBis (A B : P) (l : Line P) (h : B ≠ A) : Prop where
  dist : ∀ x : P, x LiesOn l → dist x A =dist x B

--构造中垂线,为过线段中点且与线段垂直的直线.
def PerpBis (A B : P) (h : B ≠ A) :=
  perp_line (midpoint ℝ A B) (Line.mk_pt_pt A B h)

--证明点在我们构造的中垂线上当且仅当其到两顶点相等的前置引理.
def perptr1 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ): Triangle P where
  point₁:= (SEG A B).midpoint
  point₂:= A
  point₃:= C

lemma ND_mid (A B : P)(h : B ≠ A): A ≠ (SEG A B).midpoint ∧ B ≠ (SEG A B).midpoint :=by
  constructor
  rw [ne_comm]
  exact (SEG_nd A B h).midpt_ne_source
  rw [ne_comm]
  exact (SEG_nd A B h).midpt_ne_target

lemma angle_eq_half_pi (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint):
  (ANG A (SEG A B).midpoint C (ND_mid A B h).1 k.2).value = π/(2:ℝ) := by
    sorry --不知道有没有用


lemma ND_tr(A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint):
  ¬ Collinear (SEG A B).midpoint A C := by
    sorry
    --可以尝试用 collinear_iff_toProj_eq_of_ptNe

def perptrND1 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ): TriangleND P where
  val := perptr1 A B C h k
  property :=by exact ND_tr A B C h k

def perptr2 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ): Triangle P where
  point₁:= (SEG A B).midpoint
  point₂:= B
  point₃:= C

def perptrND2 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ): TriangleND P where
  val := perptr2 A B C h k
  property := by sorry

--证明角边角分别相等
lemma edge2_eq_edge2 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ) :
  (perptr1 A B C h k).edge₂.length = (perptr2 A B C h k).edge₂.length := by
    dsimp [perptr1, perptr2, Seg.midpoint]
    rw [Triangle.edge₂]
    rw [Triangle.edge₂]

lemma edge3_eq_edge3 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ) :
  (perptr1 A B C h k).edge₃.length = (perptr2 A B C h k).edge₃.length := by
    dsimp [perptr1, perptr2, Seg.midpoint]
    repeat rw [Triangle.edge₃]
    dsimp
    rw [← Seg.length_eq_dist, ← Seg.length_eq_dist]
    have h1 : (SEG ((1 / 2 : ℝ ) • VEC A B +ᵥ A) A).length = (SEG A ((SEG A B).midpoint) ).length := by
      rw [length_of_rev_eq_length']
      dsimp [Seg.midpoint]
    have h2 : (SEG ((1 / 2 : ℝ ) • VEC A B +ᵥ A) B).length = (SEG B ((SEG A B).midpoint)).length := by
      rw [length_of_rev_eq_length']
      dsimp [Seg.midpoint]
    have h3: (SEG A ((SEG A B).midpoint) ).length = (SEG B ((SEG A B).midpoint)).length := by
      have h4: (SEG (SEG A B).source ((SEG A B).midpoint) ).length = (SEG ((SEG A B).midpoint) (SEG A B).target).length:= by
        rw [Seg.dist_target_eq_dist_source_of_midpt]
      have h5: (SEG A B).source = A :=by rfl
      have h6: (SEG A B).target = B :=by rfl
      rw [h5, h6] at h4
      rw [h4]
      exact h2
    rw [h1, h2, h3]

lemma angle_eq_neg_angle (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ) :
  (perptrND1 A B C h k).angle₁.value = - (perptrND2 A B C h k).angle₁.value := by sorry

theorem perptr1_acongr_perptr2 (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ) :
  TriangleND.IsACongr (perptrND1 A B C h k) (perptrND2 A B C h k)  :=by
  exact TriangleND.acongr_of_SAS (edge2_eq_edge2 A B C h k)  (angle_eq_neg_angle A B C h k) (edge3_eq_edge3 A B C h k)

lemma CA_eq_CB (A B C : P)(h : B ≠ A)(k: C LiesOn PerpBis A B h ∧ C ≠ (SEG A B).midpoint ) :
  dist C A = dist C B :=
  calc
    dist C A = (perptrND1 A B C h k).edge₁.length := by
      dsimp [perptrND1, TriangleND.edge₁, Triangle.edge₁, perptr1]
      exact dist_comm C A
    _ = (perptrND2 A B C h k).edge₁.length := by
      exact (perptr1_acongr_perptr2 A B C h k).edge₁
    _ = dist C B := by
      dsimp [perptrND2, TriangleND.edge₁, Triangle.edge₁, perptr2]
      exact dist_comm B C

--证明A B C共线、A ≠ C、AB = BC能推出向量AB=向量BC
theorem collinear_dist_eq_vec_eq (A B C : P) (hac : A ≠ C) (h : Collinear A B C) (h' : dist B A = dist B C) : VEC A B = VEC B C := by sorry

--vec相等推出dist相等
theorem vec_eq_dist_eq (A B C D : P) : VEC A B = VEC C D → dist A B = dist C D := by sorry

theorem lies_on_perp_iff_perp (A B : P) (l : Line P) (h : B ≠ A) : Perpendicular (LIN A B h) l ↔ B LiesOn perp_line A l := by sorry

theorem smul_left_inj (a b : ℝ) (v : Vec) (h : v ≠ 0) : a • v = b • v → a = b := by
  intro h'
  rw [← sub_eq_zero, ← sub_smul] at h'; rw [← sub_eq_zero]
  rw [smul_eq_zero_iff_left] at h'
  · exact h'
  · exact h

theorem line_line_perp_if_ang_eq_neg (A B H C: P) (h : A ≠ H ∧ B ≠ H) (hch : C ≠ H) (hba : B ≠ A) (hh : H LiesOn SEG_nd A B hba)
    (h : (ANG C H A hch h.1).value = -(ANG C H B hch h.2).value) : Perpendicular (LIN H C hch) (LIN A B hba) := by sorry

--证明点C到非退化线段AB两端距离相等时，设M为AB中点，则C M A共线或C M B共线推出C=M （为了在后面用反证法证明CMA CMB不共线）
lemma collinear_iff_midpoint_if_dist_pt_left_eq_fist_pt_right (A B C: P) (h : (SEG A B).IsND) (h' : dist C A = dist C B) :
    Collinear C (SegND.mk A B h).midpoint A → C = (SegND.mk A B h).midpoint := by
    let M := (SegND.mk A B h).midpoint
    intro CMA_coll
    rw [SegND.eq_midpt_iff_in_seg_and_dist_target_eq_dist_source]
    constructor
    · apply Collinear.perm₃₂₁ at CMA_coll
      have AMB_coll : Collinear A M B := by
        have lem : M LiesOn (SEG A B) := Seg.midpt_lies_on
        apply Seg.collinear_of_lies_on (seg := SEG A B)
        · exact Seg.source_lies_on
        · exact lem
        · exact Seg.target_lies_on
      have MA_PtNe : PtNe M A := by rw [PtNe]; exact ⟨SegND.midpt_ne_source⟩
      have CAB_coll : Collinear A B C := by
        apply collinear_of_collinear_collinear_ne AMB_coll CMA_coll
      -- 以上证明了ABC共线，接下来证明C在SEG_nd A B上
      rw [SegND.lies_on_iff]
      use 1 / 2
      constructor; norm_num; constructor; norm_num
      show VEC A C = ((1 : ℝ) / 2) • VEC A B
      have aux : C ≠ B ∧ A ≠ C ∧ B ≠ A := by
        constructor
        · by_contra cb
          rw [cb, dist_self] at h'
          apply eq_of_dist_eq_zero at h'
          rw [h'] at cb
          exact h h'
        · constructor
          · by_contra ac
            rw [← ac, dist_self] at h'
            symm at h'
            apply eq_of_dist_eq_zero at h'
            exact h h'.symm
          · exact h
      have : VecND.toProj (VEC_nd A B aux.2.2) = VecND.toProj (VEC_nd A C aux.2.1.symm) := by
        have : ¬ ((C = B) ∨ (A = C) ∨ (B = A)) := by tauto
        dsimp only [Collinear] at CAB_coll
        rw [dif_neg this] at CAB_coll
        exact CAB_coll
      symm at this; rw [VecND.toProj_eq_toProj_iff] at this
      rcases this with ⟨a, ha⟩
      have aux_acab : VEC A C = a • VEC A B := ha
      have : VecND.toProj (VEC_nd B A aux.2.2.symm) = VecND.toProj (VEC_nd B C aux.1) := by
        have : ¬ ((C = A) ∨ (B = C) ∨ (A = B)) := by tauto
        apply Collinear.perm₂₁₃ at CAB_coll
        dsimp only [Collinear] at CAB_coll
        rw [dif_neg this] at CAB_coll
        exact CAB_coll
      symm at this; rw [VecND.toProj_eq_toProj_iff] at this
      rcases this with ⟨b, hb⟩
      have aux_cbab : VEC C B = b • VEC A B := by
        have : VEC B C = b • VEC B A := hb
        rw [← neg_vec, ← neg_vec B A]
        rw [smul_neg, neg_inj]; exact this
      -- 以上证明了存在AC = a • AB和BC = b • BA
      have aux_aceqcb : VEC A C = VEC C B := by
        apply Collinear.perm₁₃₂ at CAB_coll
        exact collinear_dist_eq_vec_eq (hac := aux.2.2.symm) (h := CAB_coll) (h' := h')
      rw [aux_acab, aux_cbab] at aux_aceqcb
      have aux_ab1 : a = b := by
        apply smul_left_inj a b (VEC A B)
        · rw [← ne_iff_vec_ne_zero]; exact aux.2.2
        · exact aux_aceqcb
      have aux_ab2 : a + b = 1 := by
        have : VEC A C + VEC C B = a • VEC A B + b • VEC A B := by
          rw [← add_right_inj (VEC A C)] at aux_cbab
          nth_rw 2 [aux_acab] at aux_cbab
          exact aux_cbab
        have : VEC A B = (a + b) • VEC A B := by
          nth_rw 1 [← vec_add_vec A C B]
          rw [add_smul]; exact this
        nth_rw 1 [← one_smul ℝ (VEC A B)] at this
        apply smul_left_inj (a + b) 1 (VEC A B)
        · rw [← ne_iff_vec_ne_zero]; exact aux.2.2
        · exact this.symm
      have : a = 1 / 2 := by linarith
      rw [this] at aux_acab
      exact aux_acab
    · simp only [Seg.length_eq_dist]; rw [dist_comm]; exact h'

--下面两个lemma唯一的区别是A B替换，但为了保证M（AB中点）的一致性，在第二个lemma中增加了证明AB中点=BA中点的部分。
--把这两个提出来变成单独的lemma的原因是之后可以考虑合并（但还没来得及合orz）
lemma CMA_isnd (A B C: P) (h : (SEG A B).IsND) (h' : dist C A = dist C B)
    (hcm : C ≠ (SEG_nd A B h).midpoint) :
    ¬Collinear C (SegND.mk A B h).midpoint A := by
    let AB_seg_nd := SegND.mk A B h
    let M := AB_seg_nd.midpoint
    by_contra CMA_coll
    have hcm' : C = M := by
      apply collinear_iff_midpoint_if_dist_pt_left_eq_fist_pt_right A B C
      · exact h'
      · exact CMA_coll
    apply hcm at hcm'; exact hcm'

lemma CMB_isnd (A B C: P) (h : B ≠ A) (h' : dist C A = dist C B)
    (hcm : C ≠ (SEG_nd A B h).midpoint) :
    ¬Collinear C (SegND.mk A B h).midpoint B := by
    let AB_seg_nd := SegND.mk A B h
    let M := AB_seg_nd.midpoint
    have hcm₀ : C ≠ M := hcm
    have AB_nd : (SEG A B).IsND := h
    have BA_nd : (SEG B A).IsND := h.symm
    have AB_PtNe : PtNe A B := by rw [PtNe]; symm at h; exact ⟨h⟩
    have M' : M = (SegND.mk B A BA_nd).midpoint := by
      rw [← SegND.reverse_midpt_eq_midpt]
      have rev : SegND.reverse (SEG_nd B A BA_nd) = AB_seg_nd := by simp
      rw [rev]
    rw [M'] at hcm₀
    by_contra CMB_coll
    have CMB_coll₀ : Collinear C M B := CMB_coll
    have hcm' : C = (SegND.mk B A BA_nd).midpoint := by
      apply collinear_iff_midpoint_if_dist_pt_left_eq_fist_pt_right B A C
      · rw [h']
      · rw [M'] at CMB_coll₀; exact CMB_coll₀
    apply hcm₀ at hcm'; exact hcm'

--证明点在我们构造中垂线上当且仅当其到两顶点相等
theorem point_on_PerpBis (A B C : P) (h : B ≠ A) : C LiesOn PerpBis A B h ↔ dist C A = dist C B := by
  constructor
  · intro h'
    rcases eq_or_ne C (SEG A B).midpoint  with eq | neq
    have k := Seg.dist_target_eq_dist_source_of_eq_midpt eq
    dsimp at k
    rw [← k]
    exact dist_comm C A
    exact CA_eq_CB A B C h ⟨h', neq⟩
  · intro h'
    -- 各种引入
    let AB_line := LIN A B h
    have AB_nd : (SEG A B).IsND := h
    have BA_nd : (SEG B A).IsND := by symm at h; exact h
    have AB_PtNe : PtNe A B := by rw [PtNe]; symm at h; exact ⟨h⟩
    let AB_seg_nd := SegND.mk A B AB_nd
    let M := AB_seg_nd.midpoint
    have MA_nd : (SEG M A).IsND := by rw [Seg.IsND]; symm; apply SegND.midpt_ne_source
    have MB_nd : (SEG M B).IsND := by rw [Seg.IsND]; symm; apply SegND.midpt_ne_target
    have ham : A ≠ M := MA_nd
    have hbm : B ≠ M := MB_nd
    -- 开始证明
    by_cases hcm : C = M
    · rw [hcm]           -- 退化(C = M)
      unfold PerpBis perp_line
      rw [MID]
      exact Line.pt_lies_on_of_mk_pt_proj M AB_line.toProj.perp
    · rw [← Ne.def] at hcm               -- 非退化(C ≠ M)
      have CM_PtNe : PtNe C M := by rw [PtNe]; exact ⟨hcm⟩
      let MC := LIN M C hcm
      have CMA_isnd' : ¬Collinear C M A:= by apply CMA_isnd A B C; assumption'
      have CMB_isnd' : ¬Collinear C M B := by apply CMB_isnd A B C; assumption'
      let CMA_nd := TriangleND.mk C M A CMA_isnd'
      let CMB_nd := TriangleND.mk C M B CMB_isnd'
      -- 下面证明三条边相等
      have edge₁_eq : CMA_nd.edge₁.length = CMB_nd.edge₁.length := by
        rw [Seg.length_eq_dist, Seg.length_eq_dist]
        have : dist M A = dist M B := by
          rw [dist_comm]
          apply vec_eq_dist_eq
          exact SegND.vec_midpt_eq
        exact this
      have edge₂_eq : CMA_nd.edge₂.length = CMB_nd.edge₂.length := by
        rw [Seg.length_eq_dist, Seg.length_eq_dist]    -- 理论上来说应该能simp的、、上面还用过来着不知道为什么不行了
        rw [dist_comm C A, dist_comm C B] at h'
        exact h'
      have edge₃_eq : CMA_nd.edge₃.length = CMB_nd.edge₃.length := by
        rw [Seg.length_eq_dist, Seg.length_eq_dist]; rfl
      -- 下一行应证明CMA与CMB全等。困难之处在于EG库里的SSS只能推出Congr或ACongr，而要证明ACongr还需讨论两个三角形的方向，所以先sorry了（）
      have CMA_congr_CMB : TriangleND.IsACongr CMA_nd CMB_nd := by sorry
      have MC_perp_AB : Perpendicular MC AB_line := by
        apply line_line_perp_if_ang_eq_neg
        · apply Seg.midpt_lies_on
        · have : CMA_nd.angle₂.value = (ANG C M A hcm ham).value := by sorry
          rw [← this]
          have : CMB_nd.angle₂.value = (ANG C M B hcm hbm).value := by sorry
          rw [← this]
          exact CMA_congr_CMB.angle₂
          · exact ⟨ham, hbm⟩        --本来应该是3goals的但是不能把缩进往前一格，不知道为什么orz
      unfold PerpBis
      rw [MID]
      rw [← lies_on_perp_iff_perp]
      exact MC_perp_AB

--证明中垂线存在唯一性,即直线满足中垂线的性质当且仅当它是我们构造的那条中垂线.
theorem PerpBis_Iff_PerpBis (A B : P) (l : Line P) (h : B ≠ A) : Is_PerpBis A B l h ↔ l = PerpBis A B h := by
  constructor
  · intro h'
    have h'1 := h'.1
    rcases with l
    rcases l.nontriv with ⟨P, Q, ⟨Pl, Ql, PneqQ⟩⟩
    have Pperp : P LiesOn PerpBis A B h := by rw [point_on_PerpBis]; apply h'1 P; exact Pl
    have Qperp : Q LiesOn PerpBis A B h := by rw [point_on_PerpBis]; apply h'1 Q; exact Ql
    have PQ_PtNe : PtNe Q P := by unfold PtNe; rw [fact_iff]; exact PneqQ
    apply Line.eq_of_pt_pt_lies_on_of_ne (A := P) (B := Q)
    repeat' assumption
  · intro h'
    constructor
    intro C
    rw [h', point_on_PerpBis]
    intro _; assumption

--定义外接圆为经过三角形三顶点的圆.
structure Is_Circumcircle (tr : TriangleND P) (ω : Circle P) : Prop where
  radius1 : dist ω.center tr.1.1 = ω.radius
  radius2 : dist ω.center tr.1.2 = ω.radius
  radius3 : dist ω.center tr.1.3 = ω.radius

--定义外心为到三顶点距离相等的点.
structure Is_Circumcenter (tr : TriangleND P) (O : P) : Prop where
  dist1 : dist O tr.1.1 = dist O tr.1.2
  dist2 : dist O tr.1.2 = dist O tr.1.3
  dist3 : dist O tr.1.3 = dist O tr.1.1

--引理:三角形两边中垂线不平行.
lemma aux_PerpBis (tr : TriangleND P) :
    ¬ (PerpBis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) ∥ (PerpBis tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) := by
  repeat rw [PerpBis]
  --记三角形为ABC,将AB与AC边的中垂线记为lb,lc.
  let AB := Line.mk_pt_pt tr.1.1 tr.1.2  (ne_of_not_collinear tr.2).2.2
  let CA := Line.mk_pt_pt tr.1.3 tr.1.1  (ne_of_not_collinear tr.2).2.1
  let lb := perp_line (midpoint ℝ tr.1.1 tr.1.2) AB
  let lc := perp_line (midpoint ℝ tr.1.3 tr.1.1) CA
  show ¬ lb ∥ lc
  --使用反证法,目的是利用lb,lc平行推出AB,AC平行,由此导出矛盾.
  by_contra h
  have hb : lb ⟂ AB := perp_line_perp (midpoint ℝ tr.1.1 tr.1.2) AB
  have hc : lc ⟂ CA := perp_line_perp (midpoint ℝ tr.1.3 tr.1.1) CA
  have := hb.symm
  have := perp_of_perp_parallel this h
  have := parallel_of_perp_perp this hc
  exact Not_Para_if_nd tr this

--构造外心:为三角形两边中垂线的交点.
def Circumcenter (tr : TriangleND P) : P :=
  Line.inx (PerpBis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) (PerpBis tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1) (aux_PerpBis tr)

--证明我们构造的外心满足外心三条性质.
theorem Circumcenter_Is_Circumcenter (tr : TriangleND P) :
    Is_Circumcenter tr (Circumcenter tr) := by
  let O := Circumcenter tr
  let l1 := PerpBis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2
  let l2 := PerpBis tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1
  have ab : dist O tr.1.1 = dist O tr.1.2 := by
    have h1 : O LiesOn l1 := Line.inx_lies_on_fst (aux_PerpBis tr)
    have h2 : Is_PerpBis tr.1.1 tr.1.2 l1 (ne_of_not_collinear tr.2).2.2 := by rw [PerpBis_Iff_PerpBis]
    exact h2.1 O h1
  have ca : dist O tr.1.3 = dist O tr.1.1 := by
    have h1 : O LiesOn l2 := Line.inx_lies_on_snd (aux_PerpBis tr)
    have h2 : Is_PerpBis tr.1.3 tr.1.1 l2 (ne_of_not_collinear tr.2).2.1 := by rw [PerpBis_Iff_PerpBis]
    exact h2.1 O h1
  constructor
  · exact ab
  · rw [ab] at ca
    exact ca.symm
  · exact ca

--构造外接圆:圆心为上述外心,半径为外心与顶点A的距离.
def Circumcircle (tr : TriangleND P) : Circle P where
  center := Circumcenter tr
  radius := dist (Circumcenter tr) tr.1.1
  rad_pos := by --圆定义里需要证明半径为正
    by_contra! h
    have := Circumcenter_Is_Circumcenter tr
    have h1 : dist (Circumcenter tr) tr.1.1 = 0 := le_antisymm h dist_nonneg
    have h2 : dist (Circumcenter tr) tr.1.2 = 0 := by rw [← this.1]; exact h1
    apply eq_of_dist_eq_zero at h1
    apply eq_of_dist_eq_zero at h2
    rw [h2] at h1
    apply (ne_of_not_collinear tr.2).2.2 at h1
    exact h1

--证明我们构造的外接圆确实满足structure上三条性质
theorem Circumcircle_Is_Circumcircle (tr : TriangleND P) : Is_Circumcircle tr (Circumcircle tr) := by
  let ω := Circumcircle tr
  have h : Is_Circumcenter tr ω.1 := Circumcenter_Is_Circumcenter tr
  constructor
  · rfl
  · rw [h.2, h.3]
    rfl
  · rw [h.3]
    rfl

--证明外心的唯一性.
theorem Circumcenter_iff_Is_Circumcenter (tr : TriangleND P) (O : P) : Is_Circumcenter tr O ↔ O = Circumcenter tr := by
  constructor
  · intro h
    let l2 := PerpBis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2
    let l3 := PerpBis tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1
    have h2 : O LiesOn l2 := by
      rw [point_on_PerpBis]
      exact h.1
    have h3 : O LiesOn l3 := by
      rw [point_on_PerpBis]
      exact h.3
    have := exists_unique_intersection_of_nonparallel_lines (aux_PerpBis tr)
    rcases this with ⟨p, _, h'⟩
    have h'2 := h' O ⟨h2, h3⟩
    have h'3 := h' (Circumcenter tr) ⟨Line.inx_lies_on_fst (aux_PerpBis tr), Line.inx_lies_on_snd (aux_PerpBis tr)⟩
    rw [h'2]
    exact h'3.symm
  · intro h
    rw [h]
    exact Circumcenter_Is_Circumcenter tr

--构造九点圆,考虑定义其圆心为外心与垂心连线中点,半径为外接圆半径一半,然后在证明九个点位于该圆上.
def Nine_Point_Center (tr : TriangleND P) : P := midpoint ℝ (Circumcenter tr) (Orthocenter tr)

def Nine_Point_Circle (tr : TriangleND P) : Circle P where
  center := Nine_Point_Center tr
  radius := (Circumcircle tr).2 / 2
  rad_pos := by linarith [(Circumcircle tr).3]

--证明垂心、外心、九点圆在三角形顶点的轮换下保持不变
lemma aux1 {tr : TriangleND P} : Orthocenter tr.perm_vertices = Orthocenter tr := by
  let H := Orthocenter tr
  let H' := Orthocenter tr.perm_vertices
  show H' = H
  have := exists_unique_intersection_of_nonparallel_lines (Height₁₂_not_para tr)
  rcases this with ⟨p, _, h⟩
  have h1 : H LiesOn Height_Line₁ tr ∧ H LiesOn Height_Line₂ tr := ⟨Orthocenter_on_height tr, Orthocenter_on_height' tr⟩
  apply h at h1
  have h2 : H' LiesOn Height_Line₁ tr ∧ H' LiesOn Height_Line₂ tr := ⟨Orthocenter_on_height'' tr.perm_vertices, Orthocenter_on_height tr.perm_vertices⟩
  apply h at h2
  rw [h1]
  exact h2

lemma aux2 {tr : TriangleND P} : Circumcenter tr.perm_vertices = Circumcenter tr := by
  let O := Circumcenter tr
  let O' := Circumcenter tr.perm_vertices
  show O' = O
  let l1 := PerpBis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2
  let l2 := PerpBis tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1
  have h1 := Circumcenter_Is_Circumcenter tr
  have ho1 : O LiesOn l1 := Line.inx_lies_on_fst (aux_PerpBis tr)
  have ho2 : O LiesOn l2 := by rw [point_on_PerpBis]; exact h1.2
  have ho : O LiesOn l2 ∧ O LiesOn l1 := ⟨ho2, ho1⟩
  have ho'1 : O' LiesOn l1 := by
    have := Line.inx_lies_on_snd (aux_PerpBis tr.perm_vertices)
    exact this
  have ho'2 : O' LiesOn l2 := by
    have := Line.inx_lies_on_fst (aux_PerpBis tr.perm_vertices)
    exact this
  have ho' : O' LiesOn l2 ∧ O' LiesOn l1 := ⟨ho'2, ho'1⟩
  have := exists_unique_intersection_of_nonparallel_lines (aux_PerpBis tr.perm_vertices)
  rcases this with ⟨p, _, hp⟩
  apply hp at ho
  apply hp at ho'
  rw [ho]
  exact ho'

lemma aux3 {tr : TriangleND P} : Nine_Point_Center tr.perm_vertices = Nine_Point_Center tr := by
  rw [Nine_Point_Center]
  rw [aux1, aux2]
  rfl

lemma aux4 (tr : TriangleND P) : Nine_Point_Circle tr.perm_vertices = Nine_Point_Circle tr := by
  ext
  · exact aux3
  · show (Circumcircle tr.perm_vertices).2 / 2 = (Circumcircle tr).2 / 2
    field_simp
    calc
      (Circumcircle (TriangleND.perm_vertices tr)).radius = dist (Circumcenter tr) tr.perm_vertices.1.1 := by rw [← aux2]; rfl
      _ = dist (Circumcenter tr) tr.1.1 := by rw [(Circumcenter_Is_Circumcenter tr).1]; rfl
      _ = (Circumcircle tr).radius := rfl

--需要证明直角三角形当且仅当垂心与一顶点重合当且仅当外心与一边中点重合.
def vecnd1 (tr : TriangleND P) := (VEC_nd tr.1.3 tr.1.1 (ne_of_not_collinear tr.2).2.1)
def vecnd2 (tr : TriangleND P) := (VEC_nd tr.1.3 tr.1.2 (ne_of_not_collinear tr.2).1.symm)
def neg_vecnd1 (tr : TriangleND P) := (VEC_nd tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm)
def neg_vecnd2 (tr : TriangleND P) := (VEC_nd tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1)

lemma Height_Vertical₁ (tr : TriangleND P) : Height_Line₁ tr ⟂ ((LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1)) := by
  unfold Height_Line₁
  apply perp_line_perp tr.1.1

lemma Height_Vertical₂ (tr : TriangleND P) : Height_Line₂ tr ⟂ (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) := by
  unfold Height_Line₂
  rw [Line.line_of_pt_pt_eq_rev]
  apply perp_line_perp tr.1.2

lemma right_angle_iff_orthocenter_is_vertice_perm (tr : TriangleND P) : (ANG tr.1.1 tr.1.3 tr.1.2).dvalue =∡[π / 2] ↔ Orthocenter tr = tr.1.3 := by
  have base1 : (VecND.angle (vecnd1 tr) (vecnd2 tr)) = (ANG tr.1.1 tr.1.3 tr.1.2).dvalue := by rw [vecnd1, vecnd2]; rfl
  have base2_1_lieson_h1 : tr.1.1 LiesOn (Height_Line₁ tr) := by
    unfold Height_Line₁ perp_line
    apply Line.pt_lies_on_of_mk_pt_dir tr.1.1
  have base2_1_lieson_13 : tr.1.1 LiesOn (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) := Line.fst_pt_lies_on_mk_pt_pt
  have base2_3_lieson_13 : tr.1.3 LiesOn (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) := Line.snd_pt_lies_on_mk_pt_pt
  have base3_2_lieson_h2 : tr.1.2 LiesOn (Height_Line₂ tr) := by
    unfold Height_Line₂ perp_line
    apply Line.pt_lies_on_of_mk_pt_dir tr.1.2
  have base3_2_lieson_23 : tr.1.2 LiesOn (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := Line.fst_pt_lies_on_mk_pt_pt
  have : tr.1.3 LiesOn (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := Line.snd_pt_lies_on_mk_pt_pt
---------------------------------------------------------------------------------------
  have h : (ANG tr.1.1 tr.1.3 tr.1.2).dvalue =∡[π / 2] ↔ ⟪(vecnd1 tr).1, (vecnd2 tr).1⟫_ℝ = 0 := by
    constructor
    · intro hl
      have hl1 : (VecND.angle (vecnd1 tr) (vecnd2 tr)).cos = (0 : ℝ) := by
        rw [← base1] at hl
        have : (VecND.angle (vecnd1 tr) (vecnd2 tr) : AngValue) = (π / 2 : ℝ) ∨ (VecND.angle (vecnd1 tr) (vecnd2 tr) : AngValue) = (- π / 2 : ℝ) := by
          apply AngValue.coe_eq_pi_div_two_iff.1
          assumption
        rcases this with pos | neg
        · rw [pos]; norm_num
        · rw [neg]; norm_num; rw [neg_div, Real.cos_neg]; norm_num
      rw [← VecND.norm_mul_cos (vecnd1 tr) (vecnd2 tr), hl1]; linarith
    · intro hr
      have : ‖(vecnd1 tr)‖ ≠ 0 := by apply VecND.norm_ne_zero
      have : ‖(vecnd2 tr)‖ ≠ 0 := by apply VecND.norm_ne_zero
      have hr3 : (VecND.angle (vecnd1 tr) (vecnd2 tr)).cos = 0 := by
        by_contra hr3c; push_neg at hr3c
        have : ⟪(vecnd1 tr).1, (vecnd2 tr).1⟫_ℝ ≠ 0 := by
          rw [← VecND.norm_mul_cos (vecnd1 tr) (vecnd2 tr)]
          norm_num; exact hr3c
        contradiction
      have : (ANG tr.1.1 tr.1.3 tr.1.2).dvalue =∡[π / 2] := by
        apply AngValue.coe_eq_pi_div_two_iff.2
        apply Real.Angle.cos_eq_zero_iff.1 at hr3
        exact hr3
      exact this
  have i : ⟪(vecnd1 tr).1, (vecnd2 tr).1⟫_ℝ = 0 ↔ (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) ⟂ (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := by
    have i0 : ⟪(vecnd1 tr).1, (vecnd2 tr).1⟫_ℝ = 0 ↔ ⟪(neg_vecnd1 tr).1, (neg_vecnd2 tr).1⟫_ℝ = 0 := by
      have i01 : (vecnd1 tr).1 = -(neg_vecnd1 tr).1 := by
        unfold vecnd1 neg_vecnd1
        rw [← VecND.neg_vecND tr.1.1 tr.1.3]; rfl
      have i02 : (vecnd2 tr).1 = -(neg_vecnd2 tr).1 := by
        unfold vecnd2 neg_vecnd2
        rw [← VecND.neg_vecND tr.1.2 tr.1.3]; rfl
      rw [i01, i02]
      rw [inner_neg_neg (neg_vecnd1 tr).1 (neg_vecnd2 tr).1]
    unfold Perpendicular
    have i1 : (neg_vecnd1 tr) = toProj (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) := by
      apply Proj_eq_for_line_and_vec
      exact (ne_of_not_collinear tr.2).2.1.symm
    have i2 : (neg_vecnd2 tr) = toProj (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := by
      apply Proj_eq_for_line_and_vec
      exact (ne_of_not_collinear tr.2).1
    constructor
    · intro il
      rw [i0] at il
      apply perp_of_inner_product_eq_zero (neg_vecnd1 tr) (neg_vecnd2 tr) il
    · intro ir
      rw [i0]
      rw [← i1, ← i2] at ir
      apply inner_product_eq_zero_of_perp (neg_vecnd1 tr) (neg_vecnd2 tr) ir
  have j : (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) ⟂ (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) ↔ Orthocenter tr = tr.1.3 := by
    constructor
    · intro jl
      have jl1 : (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) = (Height_Line₁ tr) := by
        have : (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) ∥ (Height_Line₁ tr) := by
          apply parallel_of_perp_perp jl (Height_Vertical₁ tr).symm
        apply eq_of_parallel_and_pt_lies_on base2_1_lieson_13 base2_1_lieson_h1 this
      have jl2 : (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) = (Height_Line₂ tr) := by
        have : (LIN tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) ∥ (Height_Line₂ tr) := by
          apply parallel_of_perp_perp jl.symm
          apply Perpendicular.symm (Height_Vertical₂ tr)
        apply eq_of_parallel_and_pt_lies_on base3_2_lieson_23 base3_2_lieson_h2 this
      unfold Orthocenter
      have jl3 : tr.1.3 LiesOn (Height_Line₁ tr) := by
        rw [← jl1]
        apply Line.snd_pt_lies_on_mk_pt_pt
      have jl4 : tr.1.3 LiesOn (Height_Line₂ tr) := by
        rw [← jl2]
        apply Line.snd_pt_lies_on_mk_pt_pt
      have : is_inx tr.1.3 (Height_Line₁ tr) (Height_Line₂ tr) := by
        unfold is_inx
        constructor
        repeat
          · assumption
      apply unique_of_inx_of_line_of_not_para (Height₁₂_not_para tr)
      · unfold is_inx
        constructor
        repeat
        · assumption
      · unfold is_inx
        constructor
        · apply Line.inx_lies_on_fst
        · apply Line.inx_lies_on_snd
    · intro jr
      have jr1 : tr.1.3 LiesOn Height_Line₁ tr := by
        rw [← jr]
        exact Orthocenter_on_height tr
      have jr4 : (LIN tr.1.1 tr.1.3 (ne_of_not_collinear tr.2).2.1.symm) = Height_Line₁ tr := by
        rw [Line.eq_of_pt_pt_lies_on_of_ne base2_1_lieson_h1 jr1 base2_1_lieson_13 base2_3_lieson_13]
      rw [jr4]
      unfold Height_Line₁; rfl
  exact (Iff.iff h (id (Iff.symm j))).mpr i

lemma right_angle_iff_orthocenter_is_vertice (tr : TriangleND P) : (ANG tr.1.2 tr.1.1 tr.1.3).dvalue =∡[π / 2] ↔ Orthocenter tr = tr.1.1 := by
  rw [← aux1]
  apply right_angle_iff_orthocenter_is_vertice_perm tr.perm_vertices

lemma right_angle_iff_circumcenter_is_midpoint (tr : TriangleND P) : (ANG tr.1.2 tr.1.1 tr.1.3).dvalue =∡[π / 2] ↔ Circumcenter tr = midpoint ℝ tr.1.2 tr.1.3 := by sorry

--需要证明直角三角形斜边中线长度为斜边一半.

--需要等腰三角形相关引理.

--该引理在证明三角形一边中点位于九点圆上时可能会用到,但非必须.
--需要证明一顶点到垂心的距离等于外心到对边中点距离一半,需要讨论直角、锐角与钝角三角形各种情况.
--lemma dist_of_vertice_and_Orthocenter (tr : TriangleND P) : dist tr.1.1 (Orthocenter tr) = 2 * dist (midpoint ℝ tr.1.2 tr.1.3) (Circumcenter tr) := sorry

--下述三个引理证明会遇到两种退化条件,等腰三角形(困难)和直角三角形.

--引理:三角形顶点与垂心连线的中点位于九点圆上
lemma aux (tr : TriangleND P) :
    Circle.IsOn (midpoint ℝ tr.1.1 (Orthocenter tr)) (Nine_Point_Circle tr) := by
  --垂心H,外心O,九点圆V,垂心与顶点连线中点S.
  let H := Orthocenter tr
  let O := Circumcenter tr
  let V := Nine_Point_Circle tr
  let S := midpoint ℝ tr.1.1 H
  --首先分直角三角形与非直角三角形(需要先证明直角三角形相关性质)
  by_cases perp : (ANG tr.1.2 tr.1.1 tr.1.3).dvalue =∡[π / 2]
  --直角三角形,此时垂心与顶点A重合.
  · have h : H = tr.1.1 := by rw [right_angle_iff_orthocenter_is_vertice] at perp; exact perp
    have v : S = tr.1.1 := by
      calc
        S = midpoint ℝ tr.1.1 H := rfl
        _ = midpoint ℝ tr.1.1 tr.1.1 := by rw [h]
        _ = tr.1.1 := by apply midpoint_self
    show dist V.1 S = dist O tr.1.1 / 2
    have : dist V.1 H = ‖(2 : ℝ)‖⁻¹ * (dist O H) := by apply dist_midpoint_right
    rw [h] at this
    rw [v, this]
    field_simp
  --非直角三角形,再分等腰与非等腰三角形(等腰三角形情形是困难的,点在同一直线上,但位置关系不确定,情况十分复杂).
  by_cases iso : tr.edge₂.length = tr.edge₃.length
  · sorry
  --非直角+非等腰,此时顶点1,H,O不共线
  have nc : ¬ Collinear tr.1.1 H O := by sorry
  have nc' : ¬ Collinear S H V.1 := by sorry
  let tr1 := TriangleND.mk tr.1.1 H O nc
  let tr2 := TriangleND.mk S H V.1 nc'
  have sim : IsSim tr1 tr2 := by
    apply sim_of_SAS
    · sorry
    · sorry
  have h : dist V.1 S = (dist O tr.1.1) / 2 := by sorry
  exact h

--引理:三角形一边中点位于九点圆上
lemma midpoint_on_nine_point_circle (tr : TriangleND P):
    Circle.IsOn (midpoint ℝ tr.1.2 tr.1.3) (Nine_Point_Circle tr) := by
  --垂心H,外心O,九点圆V,中点M.
  let H := Orthocenter tr
  let O := Circumcenter tr
  let V := Nine_Point_Circle tr
  let M := midpoint ℝ tr.1.2 tr.1.3
  --首先分直角三角形与非直角三角形(需要先证明直角三角形相关性质)
  by_cases perp : (ANG tr.1.2 tr.1.1 tr.1.3).dvalue =∡[π / 2]
  --直角三角形,此时O与M重合,H与A重合
  · have o : O = M := by rw [right_angle_iff_circumcenter_is_midpoint] at perp; exact perp
    have h : H = tr.1.1 := by rw [right_angle_iff_orthocenter_is_vertice] at perp; exact perp
    show dist V.1 M =dist O tr.1.1 / 2
    have : dist V.1 O = ‖(2 : ℝ)‖⁻¹ * (dist O H) := by apply dist_midpoint_left
    rw [← o, ← h, this]
    field_simp
  --非直角三角形,再分等腰与非等腰三角形(等腰三角形情形是困难的,点在同一直线上,但位置关系不确定,情况十分复杂).
  by_cases iso : tr.edge₂.length = tr.edge₃.length
  · sorry
  --非直角+非等腰,此时顶点1,H,O不共线
  have nc : ¬ Collinear tr.1.1 H O := by sorry
  have nc'' : ¬ Collinear M O V.1 := by sorry
  let tr1 := TriangleND.mk tr.1.1 H O nc
  let tr3 := TriangleND.mk M O V.1 nc''
  --这里的相似并不严谨,严格而言需要根据锐角三角形(垂心在三角形内)和钝角三角形(垂心在三角形外)分类讨论,,情况复杂.
  --暂时没有更简洁的方法.
  have sim : IsSim tr1 tr3 := by
    apply sim_of_SAS
    · sorry
    · sorry
  have h : dist V.1 M = (dist O tr.1.1) / 2 := by sorry
  exact h

--引理:三角形一条高的垂足位于九点圆上
lemma perp_foot_on_nine_point_circle (tr : TriangleND P) :
    Circle.IsOn (perp_foot tr.1.1 (Line.mk_pt_pt tr.1.2 tr.1.3  (ne_of_not_collinear tr.2).1)) (Nine_Point_Circle tr) := by
  --垂心H,外心O,九点圆V,垂心与顶点连线中点S,中点M,垂足G
  let H := Orthocenter tr
  let O := Circumcenter tr
  let V := Nine_Point_Circle tr
  let S := midpoint ℝ tr.1.1 H
  let M := midpoint ℝ tr.1.2 tr.1.3
  let G := perp_foot tr.1.1 (Line.mk_pt_pt tr.1.2 tr.1.3  (ne_of_not_collinear tr.2).1)
  --首先分直角三角形与非直角三角形(需要先证明直角三角形相关性质)
  by_cases perp : (ANG tr.1.2 tr.1.1 tr.1.3).dvalue =∡[π / 2]
  --直角三角形,此时G,H,A重合.
  · have o : O = M := by rw [right_angle_iff_circumcenter_is_midpoint] at perp; exact perp
    have h : H = tr.1.1 := by rw [right_angle_iff_orthocenter_is_vertice] at perp; exact perp
    show dist V.1 G =dist O tr.1.1 / 2
    sorry
  --非直角三角形,再分等腰与非等腰三角形.
  --等腰三角形情形,垂足与中点重合,证明难度与前一引理相同.
  by_cases iso : tr.edge₂.length = tr.edge₃.length
  · sorry
  --非直角+非等腰,此时顶点1,H,O不共线
  --暂时没有简洁方法,其难度应该要高于前一引理.
  sorry

--利用九点圆的性质定义九点圆,即三边中点,三条高的垂足,三顶点与垂心连线的中点在这个圆上.
structure Is_Nine_Point_Circle (tr : TriangleND P) (V : Circle P) : Prop where
  mid1 : Circle.IsOn (midpoint ℝ tr.1.2 tr.1.3) V
  mid2 : Circle.IsOn (midpoint ℝ tr.1.3 tr.1.1) V
  mid3 : Circle.IsOn (midpoint ℝ tr.1.1 tr.1.2) V
  height1 : Circle.IsOn (perp_foot tr.1.1 (Line.mk_pt_pt tr.1.2 tr.1.3  (ne_of_not_collinear tr.2).1)) V
  height₂ : Circle.IsOn (perp_foot tr.1.2 (Line.mk_pt_pt tr.1.3 tr.1.1  (ne_of_not_collinear tr.2).2.1)) V
  height₃ : Circle.IsOn (perp_foot tr.1.3 (Line.mk_pt_pt tr.1.1 tr.1.2  (ne_of_not_collinear tr.2).2.2)) V
  mid_height₁ : Circle.IsOn (midpoint ℝ tr.1.1 (Orthocenter tr)) V
  mid_height₂ : Circle.IsOn (midpoint ℝ tr.1.2 (Orthocenter tr)) V
  mid_height₃ : Circle.IsOn (midpoint ℝ tr.1.3 (Orthocenter tr)) V

structure Is_Nine_Point_Center (tr : TriangleND P) (V : P) : Prop where

--九点圆定理即为证明我们构造出的九点圆满足九点圆的定义.
theorem NPC (tr : TriangleND P) : Is_Nine_Point_Circle tr (Nine_Point_Circle tr) := by
  constructor
  --我们对三角形及其轮换使用引理
  --三边中点
  · apply midpoint_on_nine_point_circle tr
  · have := midpoint_on_nine_point_circle tr.perm_vertices
    rw [← aux4]
    exact this
  . have := midpoint_on_nine_point_circle tr.perm_vertices.perm_vertices
    rw [← aux4, ← aux4]
    exact this
  --三条高的垂足
  · apply perp_foot_on_nine_point_circle
  · have := perp_foot_on_nine_point_circle tr.perm_vertices
    rw [← aux4]
    exact this
  · have := perp_foot_on_nine_point_circle tr.perm_vertices.perm_vertices
    rw [← aux4, ← aux4]
    exact this
  --垂心与顶点连线中点
  · apply aux
  · have := aux tr.perm_vertices
    rw [← aux4,← aux1]
    exact this
  · have := aux tr.perm_vertices.perm_vertices
    rw [← aux4, ← aux4, ← aux1, ← aux1]
    exact this
