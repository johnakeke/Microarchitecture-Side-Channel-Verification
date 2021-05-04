theory CM_SecurityModel
  imports Main "HOL.Real" "HOL.Transcendental"
          "HOL.Finite_Set"
begin

abbreviation "folds \<equiv> Finite_Set.fold"
interpretation plus_comp_fun_commute_P: comp_fun_commute "(\<lambda>t. (+) (P t::real))" apply standard by auto

subsection \<open>State Machine based on Probability\<close>

locale CM =

  (*The state domain*)
  fixes SN :: "'s set"
  fixes SE :: "'s set"

  (*The input and its probability distribution*)
  fixes input_dist :: "('i \<times> real) set"

  (*The pmf function gives conditional probability matrix W(o|i)*)
  fixes pmf :: "'i \<Rightarrow> 's \<Rightarrow> 'e \<Rightarrow> ('o \<times> real) set"

  assumes
    inputdist_finite: "finite input_dist" and
    inputdist_nonempty: "input_dist \<noteq> {}" and
    inputdist_unique: "\<forall>i j. i \<in> input_dist \<and> j \<in> input_dist \<and> i \<noteq> j \<longrightarrow> fst i \<noteq> fst j" and
    inputdist_positive: "\<forall>i \<in> input_dist. (snd i) > 0" and
    inputdist_sum_one: "folds (\<lambda>t p. snd t + p) 0 input_dist = 1" and

    pmf_finite: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SN. finite (pmf (fst i) s e)" and
    pmf_nonempty: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SN. pmf (fst i) s e \<noteq> {}" and
    pmf_unique: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SN. \<forall>m n. m \<in> pmf (fst i) s e \<and> n \<in> pmf (fst i) s e \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n" and
    pmf_positive: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SN. \<forall>d \<in> pmf (fst i) s e. snd d \<ge> 0" and
    pmf_sum_one: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (pmf (fst i) s e) = 1" and

    state_finite: "finite SN" and
    state_nonempty: "SN \<noteq> {}" and
    state_nonempty2: "SE \<noteq> {}" and
    state_subset: "SE \<subseteq> SN"

begin


subsection \<open>Joint Probability Distribution Properties\<close>

  definition makeDist :: "'s \<Rightarrow> 'e \<Rightarrow> (('i \<times> 'o) \<times> real) set"
    where "makeDist s e \<equiv> {t. \<exists>i \<in> input_dist. \<exists>d \<in> pmf (fst i) s e. t = ((fst i, fst d), snd i * snd d)}"

  (*The joint probability distribution looks like this.
          output0  output1  output02  output03  output04 ...
          --------------------------------------------------
  input0  p00      0        0         0         0                                       
          --------------------------------------------------
  input1  0        p11      0         0         0                                
          --------------------------------------------------
  input2  0        0        p22       p23       p24   
          --------------------------------------------------
  input3  0        0        p32       p33       p34   
  ...
  *)

  lemma jodist_finite: "\<forall>e. \<forall>s \<in> SN. finite (makeDist s e)"
    proof -
      {
        fix e
        have "\<forall>s \<in> SN. finite (makeDist s e)"
        proof -
          {
            fix s
            assume "s \<in> SN"
            have "finite (makeDist s e)"
            proof -
              {
                have "\<forall>i \<in> input_dist. finite (pmf (fst i) s e)"
                  using \<open>s \<in> SN\<close> pmf_finite by blast
                then have "\<forall>i \<in> input_dist. finite {t. \<exists>d \<in> pmf (fst i) s e. t = ((fst i, fst d), snd i * snd d)}"
                  by auto
                then have "finite {t. \<exists>i \<in> input_dist. \<exists>d \<in> pmf (fst i) s e. t = ((fst i, fst d), snd i * snd d)}"
                  using inputdist_finite by auto
                then show ?thesis
                  unfolding makeDist_def by auto
              }
            qed
          }
          then show ?thesis by auto
        qed
      }
      then show ?thesis by blast
    qed

  lemma jodist_nonempty: "\<forall>e. \<forall>s \<in> SN. makeDist s e \<noteq> {}"
    using makeDist_def state_nonempty inputdist_nonempty pmf_nonempty
    by (smt all_not_in_conv mem_Collect_eq)

  lemma jodist_unique: "\<forall>e. \<forall>s \<in> SN. \<forall>i j. i \<noteq> j \<and> i \<in> makeDist s e \<and> j \<in> makeDist s e \<longrightarrow> fst i \<noteq> fst j"
    using makeDist_def state_nonempty inputdist_unique pmf_unique
    by (smt Pair_inject fstI mem_Collect_eq) 

  lemma jodist_positive: "\<forall>e. \<forall>s \<in> SN. \<forall>d \<in> makeDist s e. snd d \<ge> 0"
    using makeDist_def state_nonempty inputdist_positive pmf_positive by fastforce

  lemma folds_plus_times_input:
    assumes a0: "finite (w::('i \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> w \<and> j \<in> w \<longrightarrow> fst i \<noteq> fst j"
      shows "folds (\<lambda>t p. snd t * i + p) 0 w = i * (folds (\<lambda>t p. snd t + p) 0 w)"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        have "folds (\<lambda>t p. snd t * i + p) 0 {x} = snd x * i + folds (\<lambda>t p. snd t * i + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        moreover have "folds (\<lambda>t p. snd t + p) 0 {x} = snd x + folds (\<lambda>t p. snd t + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        ultimately show ?case
          using fold_empty by auto
      next
        case (insert x F)
        have "folds (\<lambda>t p. snd t * i + p) 0 (insert x F) = snd x * i + folds (\<lambda>t p. snd t * i + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert insert.hyps(1) insert.hyps(3) by simp
        moreover have "folds (\<lambda>t p. snd t * i + p) 0 F = i * folds (\<lambda>t p. snd t + p) 0 F"
          using insert.hyps(4) insert.prems by blast
        ultimately have "folds (\<lambda>t p. snd t * i + p) 0 (insert x F) = i * (folds (\<lambda>t p. snd t + p) 0 (insert x F))"
          by (simp add: distrib_left insert.hyps(1) insert.hyps(3))
        then show ?case by auto
      qed
    qed

  lemma folds_plus_times_input2:
    assumes a0: "finite (w::('i \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> w \<and> j \<in> w \<longrightarrow> fst i \<noteq> fst j"
      shows "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>i \<in> w. t = ((fst i, fst d), snd i * snd d)} =
             folds (\<lambda>t p. snd t * snd d + p) 0 w"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct arbitrary: d rule: finite_ne_induct)
        case (singleton x)
        have "{t. \<exists>i \<in> {x}. t = ((fst i, fst d), snd i * snd d)} =
              {((fst x, fst d), snd x * snd d)}"
          by auto
        then have "folds (\<lambda>t p. snd t + p) 0 {((fst x, fst d), snd x * snd d)} =
                   (snd x * snd d) + folds (\<lambda>t p. snd t + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        moreover have "folds (\<lambda>t p. snd t * snd d + p) 0 {x} = snd x * snd d + folds (\<lambda>t p. snd t * snd d + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        ultimately show ?case by auto
      next
        case (insert x F)
        have p0: "{t. \<exists>i \<in> insert x F. t = ((fst i, fst d), snd i * snd d)} =
                  {t. \<exists>i \<in> F. t = ((fst i, fst d), snd i * snd d)} \<union> {((fst x, fst d), snd x * snd d)}"
          by auto
        have p1: "{t. \<exists>i \<in> F. t = ((fst i, fst d), snd i * snd d)} \<inter> {((fst x, fst d), snd x * snd d)} = {}"
          by (smt Pair_inject disjoint_insert(2) inf_bot_right insert.hyps(3) insert.prems insertCI mem_Collect_eq)
        have p2: "finite {t. \<exists>i \<in> F. t = ((fst i, fst d), snd i * snd d)}"
          using insert.hyps(1) by auto
        have p3: "folds (\<lambda>t p. snd t + p) 0 ({t. \<exists>i \<in> F. t = ((fst i, fst d), snd i * snd d)} \<union> {((fst x, fst d), snd x * snd d)}) =
                  folds (\<lambda>t p. snd t + p) (folds (\<lambda>t p. snd t + p) 0 {t. \<exists>i \<in> F. t = ((fst i, fst d), snd i * snd d)}) {((fst x, fst d), snd x * snd d)}"
          using plus_comp_fun_commute_P.fold_set_union_disj p2 p1 by auto 
        have p4: "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>i \<in> F. t = ((fst i, fst d), snd i * snd d)} =
                  folds (\<lambda>t p. snd t * snd d + p) 0 F"
          using insert.hyps(4) insert.prems by auto
        have p5: "folds (\<lambda>t p. snd t * snd d + p) 0 (insert x F) =
                  folds (\<lambda>t p. snd t * snd d + p) 0 {x} + folds (\<lambda>t p. snd t * snd d + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert
          by (simp add: insert.hyps(1) insert.hyps(3)) 
        show ?case using p0 p3 p4 p5 by auto 
      qed
    qed

  lemma folds_plus_times_output:
    assumes a0: "finite (w::('o \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> w \<and> j \<in> w \<longrightarrow> fst i \<noteq> fst j"
      shows "folds (\<lambda>t p. snd t * i + p) 0 w = i * (folds (\<lambda>t p. snd t + p) 0 w)"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        have "folds (\<lambda>t p. snd t * i + p) 0 {x} = snd x * i + folds (\<lambda>t p. snd t * i + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        moreover have "folds (\<lambda>t p. snd t + p) 0 {x} = snd x + folds (\<lambda>t p. snd t + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        ultimately show ?case
          using fold_empty by auto
      next
        case (insert x F)
        have "folds (\<lambda>t p. snd t * i + p) 0 (insert x F) = snd x * i + folds (\<lambda>t p. snd t * i + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert insert.hyps(1) insert.hyps(3) by simp
        moreover have "folds (\<lambda>t p. snd t * i + p) 0 F = i * folds (\<lambda>t p. snd t + p) 0 F"
          using insert.hyps(4) insert.prems by blast
        ultimately have "folds (\<lambda>t p. snd t * i + p) 0 (insert x F) = i * (folds (\<lambda>t p. snd t + p) 0 (insert x F))"
          by (simp add: distrib_left insert.hyps(1) insert.hyps(3))
        then show ?case by auto
      qed
    qed

  lemma folds_plus_times_output2:
    assumes a0: "finite (w::('o \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> w \<and> j \<in> w \<longrightarrow> fst i \<noteq> fst j"
      shows "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>d \<in> w. t = ((fst i, fst d), snd i * snd d)} =
             folds (\<lambda>t p. snd t * snd i + p) 0 w"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct arbitrary: i rule: finite_ne_induct)
        case (singleton x)
        have "{t. \<exists>d \<in> {x}. t = ((fst i, fst d), snd i * snd d)} =
              {((fst i, fst x), snd i * snd x)}"
          by auto
        then have "folds (\<lambda>t p. snd t + p) 0 {((fst i, fst x), snd i * snd x)} =
                   (snd i * snd x) + folds (\<lambda>t p. snd t + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        moreover have "folds (\<lambda>t p. snd t * snd i + p) 0 {x} = snd x * snd i + folds (\<lambda>t p. snd t * snd i + p) 0 {}"
          using plus_comp_fun_commute_P.fold_insert by simp
        ultimately show ?case by auto
      next
        case (insert x F)
        have p0: "{t. \<exists>d \<in> insert x F. t = ((fst i, fst d), snd i * snd d)} =
                  {t. \<exists>d \<in> F. t = ((fst i, fst d), snd i * snd d)} \<union> {((fst i, fst x), snd i * snd x)}"
          by auto
        have p1: "{t. \<exists>d \<in> F. t = ((fst i, fst d), snd i * snd d)} \<inter> {((fst i, fst x), snd i * snd x)} = {}"
          by (smt Pair_inject disjoint_insert(2) inf_bot_right insert.hyps(3) insert.prems insertCI mem_Collect_eq)
        have p2: "finite {t. \<exists>d \<in> F. t = ((fst i, fst d), snd i * snd d)}"
          using insert.hyps(1) by auto
        have p3: "folds (\<lambda>t p. snd t + p) 0 ({t. \<exists>d \<in> F. t = ((fst i, fst d), snd i * snd d)} \<union> {((fst i, fst x), snd i * snd x)}) =
                  folds (\<lambda>t p. snd t + p) (folds (\<lambda>t p. snd t + p) 0 {t. \<exists>d \<in> F. t = ((fst i, fst d), snd i * snd d)}) {((fst i, fst x), snd i * snd x)}"
          using plus_comp_fun_commute_P.fold_set_union_disj p2 p1 by auto 
        have p4: "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>d \<in> F. t = ((fst i, fst d), snd i * snd d)} =
                  folds (\<lambda>t p. snd t * snd i + p) 0 F"
          using insert.hyps(4) insert.prems by auto
        have p5: "folds (\<lambda>t p. snd t * snd i + p) 0 (insert x F) =
                  folds (\<lambda>t p. snd t * snd i + p) 0 {x} + folds (\<lambda>t p. snd t * snd i + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert
          by (simp add: insert.hyps(1) insert.hyps(3)) 
        show ?case using p0 p3 p4 p5 by auto 
      qed
    qed


  (*Input marginal probability distribution*)
  definition marg_input :: "(('i \<times> 'o) \<times> real) set \<Rightarrow> ('i \<times> real) set"
    where "marg_input jo_dist \<equiv> {t. \<exists>i \<in> ((fst o fst) ` jo_dist).
                                    t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> jo_dist \<and> fst (fst s) = i})}"

  lemma marg_input_finite:
    assumes a0: "finite (F::(('i \<times> 'o) \<times> real) set)"
        and a1: "F \<noteq> {}"
      shows "finite (marg_input F)"
    proof -
      show ?thesis using a0 a1
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        then show ?case
          unfolding marg_input_def by auto
      next
        case (insert x F)
        then show ?case
        proof(cases "fst (fst x) \<notin> (fst o fst) ` F")
          case True
          have p1: "(fst o fst) ` (insert x F) = {(fst (fst x))} \<union> ((fst o fst) ` F)"
            by auto
          then have p2: "marg_input (insert x F) = {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} \<union>
                                                   {t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
            unfolding marg_input_def by blast
          have "{s. s \<in> insert x F \<and> fst (fst s) = fst (fst x)} = {x}"
            using True by (smt Collect_cong comp_apply insertE insertI1 insert_image singleton_conv) 
          then have p4: "{t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} = {(fst (fst x), snd x)}"
            by force 
          have "\<forall>i \<in> ((fst o fst) ` F). folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i} =
                                        folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i}"
            using True by (smt Collect_cong insert_iff) 
          then have p5: "{t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} = marg_input F"
            unfolding marg_input_def by auto
          have "marg_input (insert x F) = (marg_input F) \<union> {(fst (fst x), snd x)}"
            using p2 p4 p5 by auto
          then show ?thesis
            by (simp add: insert.hyps(4)) 
        next
          case False
          then have p1: "(fst o fst) ` (insert x F) = ((fst o fst) ` F)"
            by (simp add: insert_absorb) 
          then have p2: "marg_input (insert x F) = {t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
            unfolding marg_input_def by auto
          have p3: "(fst o fst) ` F = {(fst (fst x))} \<union> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}"
            using False by blast
          then have p4: "marg_input (insert x F) =
                         {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} \<union>
                         {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
            using p2 by blast
          have c1: "\<forall>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. {s. s \<in> insert x F \<and> fst (fst s) = i} = {s. s \<in> F \<and> fst (fst s) = i}"
            by blast
          then have c2: "{t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} =
                         {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})}"
            by auto
          have "{t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})} \<subseteq> marg_input F"
            unfolding marg_input_def by blast 
          then have c_final: "finite {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
            using c2 by (simp add: finite_subset insert.hyps(4))
          then show ?thesis
            using p4 by simp
        qed
      qed
    qed

  lemma marg_input_insert:
    assumes a0: "finite (F::(('i \<times> 'o) \<times> real) set)"
        and a1: "F \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> F \<and> j \<in> F \<longrightarrow> fst i \<noteq> fst j"
        and a3: "\<forall>d \<in> F. fst d \<noteq> fst x"
      shows "folds (\<lambda>t p. snd t + p) 0 (marg_input (insert x F)) = snd x + folds (\<lambda>t p. snd t + p) 0 (marg_input F)"
    proof -
      show ?thesis using a0 a1 a2 a3
      proof(cases "fst (fst x) \<notin> (fst o fst) ` F")
        case True
        have p1: "(fst o fst) ` (insert x F) = {(fst (fst x))} \<union> ((fst o fst) ` F)"
          by auto
        then have p2: "marg_input (insert x F) = {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} \<union>
                                                 {t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          unfolding marg_input_def by blast
        have p3: "{t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} \<inter>
                  {t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} = {}"
          using True p1 by blast
        have "{s. s \<in> insert x F \<and> fst (fst s) = fst (fst x)} = {x}"
          using True by (smt Collect_cong comp_apply insertE insertI1 insert_image singleton_conv) 
        then have p4: "{t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} = {(fst (fst x), snd x)}"
          by force 
        have "\<forall>i \<in> ((fst o fst) ` F). folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i} =
                                      folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i}"
          using True by (smt Collect_cong insert_iff) 
        then have p5: "{t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} = marg_input F"
          unfolding marg_input_def by auto
        have "marg_input (insert x F) = (marg_input F) \<union> {(fst (fst x), snd x)}"
          using p2 p4 p5 by auto
        then have "folds (\<lambda>t p. snd t + p) 0 (marg_input (insert x F)) =
                   folds (\<lambda>t p. snd t + p) (folds (\<lambda>t p. snd t + p) 0 (marg_input F)) {(fst (fst x), snd x)}"
          using marg_input_finite a0 plus_comp_fun_commute_P.fold_set_union_disj
          proof -
            have "marg_input F \<inter> {(fst (fst x), snd x)} = {}"
              by (metis Int_commute p3 p4 p5)
            then show ?thesis
              by (simp add: \<open>marg_input (insert x F) = marg_input F \<union> {(fst (fst x), snd x)}\<close> a0 a1 marg_input_finite)
          qed
        then have "folds (\<lambda>t p. snd t + p) 0 (marg_input (insert x F)) = snd x + folds (\<lambda>t p. snd t + p) 0 (marg_input F)"
          using plus_comp_fun_commute_P.fold_insert by simp 
        then show ?thesis by auto
      next
        case False
        then have p1: "(fst o fst) ` (insert x F) = ((fst o fst) ` F)"
          by (simp add: insert_absorb) 
        then have p2: "marg_input (insert x F) = {t. \<exists>i \<in> ((fst o fst) ` F). t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          unfolding marg_input_def by auto
        have p3: "(fst o fst) ` F = {(fst (fst x))} \<union> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}"
          using False by blast
        then have p4: "marg_input (insert x F) =
                       {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} \<union>
                       {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          using p2 by blast
        have p5: "finite (marg_input (insert x F))"
          by (simp add: a0 marg_input_finite)
        have p6_1: "finite {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          by auto
        have p6_2: "finite {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          using p4 p5 by simp
        have p7: "{t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} \<inter>
                  {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} = {}"
          by auto
        have p8: "folds (\<lambda>s p. snd s + p) 0 (marg_input (insert x F)) =
                  folds (\<lambda>s p. snd s + p) (folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})})
                                          {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          using plus_comp_fun_commute_P.fold_set_union_disj p4 p6_1 p6_2 p7 by simp 
        then have p9: "folds (\<lambda>s p. snd s + p) 0 (marg_input (insert x F)) =
                       folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} +
                       folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})}"
          by simp
        have b1: "{s. s \<in> insert x F \<and> fst (fst s) = fst (fst x)} = {x} \<union> {s. s \<in> F \<and> fst (fst s) = fst (fst x)}"
          by auto
        have b2: "{x} \<inter> {s. s \<in> F \<and> fst (fst s) = fst (fst x)} = {}"
          using a3 by fastforce
        have b3: "folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = fst (fst x)} =
                  folds (\<lambda>s p. snd s + p) (folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = fst (fst x)}) {x}"
          using plus_comp_fun_commute_P.fold_set_union_disj b1 b2
          by (simp add: Collect_conj_eq a0)
        then have b4: "folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = fst (fst x)} =
                       snd x + folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = fst (fst x)}"
          by simp
        then have b_final: "folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} =
                            snd x + folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = fst (fst x)}"
          by auto
        have c1: "\<forall>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. {s. s \<in> insert x F \<and> fst (fst s) = i} = {s. s \<in> F \<and> fst (fst s) = i}"
          by blast
        then have c_final: "folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> insert x F \<and> fst (fst s) = i})} =
                            folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})}"
          by auto
        have d1: "marg_input F =
                  {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})} \<union>
                  {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})}"
          unfolding marg_input_def using p3 by blast
        have d2: "folds (\<lambda>s p. snd s + p) 0 (marg_input F) =
                  folds (\<lambda>s p. snd s + p) (folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})})
                                          {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})}"
          using plus_comp_fun_commute_P.fold_set_union_disj[where ?P = "snd"]
          by (smt Int_emptyI Un_commute a0 a1 d1 finite_Un fst_conv marg_input_finite mem_Collect_eq singletonD)
        then have d_final: "folds (\<lambda>s p. snd s + p) 0 (marg_input F) =
                            folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {d. d \<in> ((fst o fst) ` F) \<and> d \<noteq> fst (fst x)}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})} +
                            folds (\<lambda>s p. snd s + p) 0 {t. \<exists>i \<in> {(fst (fst x))}. t = (i, folds (\<lambda>s p. snd s + p) 0 {s. s \<in> F \<and> fst (fst s) = i})}"
          by simp
        have "folds (\<lambda>s p. snd s + p) 0 (marg_input (insert x F)) = snd x + folds (\<lambda>s p. snd s + p) 0 (marg_input F)"
          using p9 b_final c_final d_final by simp
        then show ?thesis by auto
      qed
    qed

  lemma jodist_marg_input_induct:
    assumes a0: "finite (jodist::(('i \<times> 'o) \<times> real) set)"
        and a1: "jodist \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> jodist \<and> j \<in> jodist \<longrightarrow> fst i \<noteq> fst j"
      shows "folds (\<lambda>t p. snd t + p) 0 jodist =
             folds (\<lambda>t p. snd t + p) 0 (marg_input jodist)"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        have "folds (\<lambda>t p. snd t + p) 0 {x} = snd x"
          by auto
        moreover have "marg_input {x} = {(fst (fst x), snd x)}"
          unfolding marg_input_def comp_def
          by (smt Collect_cong calculation image_empty image_insert singletonI singleton_conv singleton_iff) 
        ultimately have "folds (\<lambda>t p. snd t + p) 0 (marg_input {x}) = snd x"
          by auto
        then show ?case by auto
      next
        case (insert x F)
        have p1: "folds (\<lambda>t p. snd t + p) 0 (insert x F) = snd x + folds (\<lambda>t p. snd t + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert insert.hyps(1) insert.hyps(3) by simp
        have p2: "folds (\<lambda>t p. snd t + p) 0 F = folds (\<lambda>t p. snd t + p) 0 (marg_input F)"
          using insert.hyps(4) insert.prems by blast
        moreover have "\<forall>d \<in> F. fst d \<noteq> fst x"
          using jodist_unique
          by (metis DiffD1 Diff_insert_absorb insert.hyps(3) insert.prems insertI1)
        moreover have "folds (\<lambda>t p. snd t + p) 0 (marg_input (insert x F)) = snd x + folds (\<lambda>t p. snd t + p) 0 (marg_input F)"
          using marg_input_insert
          by (metis DiffD1 Diff_insert_absorb calculation(2) insert.hyps(1) insert.hyps(2) insert.prems) 
        ultimately show ?case
          using p1 by linarith
      qed
    qed

  lemma jodist_marg_input_sum:
    "\<forall>e. \<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                  folds (\<lambda>t p. snd t + p) 0 (marg_input (makeDist s e))"
    proof -
      {
        fix e
        have "\<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                       folds (\<lambda>t p. snd t + p) 0 (marg_input (makeDist s e))"
        proof -
          {
            fix s
            assume "s \<in> SN"
            have "folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                  folds (\<lambda>t p. snd t + p) 0 (marg_input (makeDist s e))"
            proof -
              {
                have "finite (makeDist s e)"
                  using \<open>s \<in> SN\<close> jodist_finite by blast
                moreover have "makeDist s e \<noteq> {}"
                  using \<open>s \<in> SN\<close> jodist_nonempty by blast
                moreover have "\<forall>i j. i \<noteq> j \<and> i \<in> (makeDist s e) \<and> j \<in> (makeDist s e) \<longrightarrow> fst i \<noteq> fst j"
                  using \<open>s \<in> SN\<close> jodist_unique by blast
                ultimately show ?thesis
                  using jodist_marg_input_induct by blast
              }
            qed
          }
          then show ?thesis by blast
        qed
      }
      then show ?thesis by blast
    qed

  lemma marg_input_unique: "\<forall>e. \<forall>s \<in> SN. \<forall>d \<in> makeDist s e. \<exists>!t \<in> marg_input (makeDist s e). fst t = fst (fst d)"
    proof -
      {
        fix e
        have "\<forall>s \<in> SN. \<forall>d \<in> makeDist s e. \<exists>!t \<in> marg_input (makeDist s e). fst t = fst (fst d)"
        proof -
          {
            fix s
            assume "s \<in> SN"
            have "\<forall>d \<in> makeDist s e. \<exists>!t \<in> marg_input (makeDist s e). fst t = fst (fst d)"
            proof -
              {
                fix d
                assume "d \<in> makeDist s e"
                have "\<exists>!t \<in> marg_input (makeDist s e). fst t = fst (fst d)"
                proof -
                  {
                    have "fst (fst d) \<in> (fst o fst) ` (makeDist s e)"
                      using \<open>d \<in> makeDist s e\<close> unfolding makeDist_def by auto
                    then have "((fst (fst d)), folds (\<lambda>s p. snd s + p) 0 {u. u \<in> (makeDist s e) \<and> fst (fst u) = fst (fst d)}) \<in> marg_input (makeDist s e)"
                      using \<open>d \<in> makeDist s e\<close> unfolding marg_input_def by blast
                    then show ?thesis
                      using marg_input_def by auto
                  }
                qed
              }
              then show ?thesis by blast
            qed
          }
          then show ?thesis by auto
        qed
      }
      then show ?thesis by blast
    qed

  lemma marg_input_fold:
    "\<forall>s \<in> SN. \<forall>i e. i \<in> input_dist \<longrightarrow> folds (\<lambda>t p. snd t + p) 0 {d. d \<in> makeDist s e \<and> fst (fst d) = fst i} = snd i"
    proof -
      {
        fix s
        assume "s \<in> SN"
        have "\<forall>i e. i \<in> input_dist \<longrightarrow> folds (\<lambda>t p. snd t + p) 0 {d. d \<in> makeDist s e \<and> fst (fst d) = fst i} = snd i"
        proof -
          {
            fix i e
            have "i \<in> input_dist \<longrightarrow> folds (\<lambda>t p. snd t + p) 0 {d. d \<in> makeDist s e \<and> fst (fst d) = fst i} = snd i"
            proof -
              {
                assume a0: "i \<in> input_dist"
                have "folds (\<lambda>t p. snd t + p) 0 {d. d \<in> makeDist s e \<and> fst (fst d) = fst i} = snd i"
                proof -
                  {
                    have p0: "folds (\<lambda>t p. snd t + p) 0 (pmf (fst i) s e) = 1"
                      using \<open>s \<in> SN\<close> a0 pmf_sum_one by blast
                    have p_dw: "{t. t \<in> makeDist s e \<and> fst (fst t) = fst i} =
                                {t. \<exists>w \<in> (pmf (fst i) s e). t = ((fst i, fst w), snd i * snd w)}"
                      unfolding makeDist_def using a0
                      by (smt Collect_cong fstI inputdist_unique mem_Collect_eq mult.commute)
                    have p1: "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>w \<in> (pmf (fst i) s e). t = ((fst i, fst w), snd i * snd w)} =
                              folds (\<lambda>t p. snd t * snd i + p) 0 (pmf (fst i) s e)"
                      using folds_plus_times_output2[where ?w = "pmf (fst i) s e" and ?i = "i"] \<open>s \<in> SN\<close> a0 pmf_finite pmf_nonempty pmf_unique
                      by blast
                    have "folds (\<lambda>t p. snd t * snd i + p) 0 (pmf (fst i) s e) =
                          snd i * (folds (\<lambda>t p. snd t + p) 0 (pmf (fst i) s e))"
                      using folds_plus_times_output \<open>s \<in> SN\<close> a0 pmf_finite pmf_nonempty pmf_unique
                      by meson
                    then have "folds (\<lambda>t p. snd t * snd i + p) 0 (pmf (fst i) s e) = snd i"
                      using p0 by (simp add: a0 inputdist_positive) 
                    then have "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>w \<in> (pmf (fst i) s e). t = ((fst i, fst w), snd i * snd w)} = snd i"
                      using p1 by auto
                    then have ?thesis using p_dw by auto
                  }
                  then show ?thesis by auto
                qed
              }
              then show ?thesis by auto
            qed
          }
          then show ?thesis by auto
        qed
      }
      then show ?thesis by auto
    qed

  lemma marg_input_sum_h1: "\<forall>s \<in> SN. \<forall>i e. i \<in> input_dist \<longrightarrow> i \<in> marg_input (makeDist s e)"
    proof -
      {
        fix s
        assume "s \<in> SN"
        have "\<forall>i e. i \<in> input_dist \<longrightarrow> i \<in> marg_input (makeDist s e)"
        proof -
          {
            fix i e
            have "i \<in> input_dist \<longrightarrow> i \<in> marg_input (makeDist s e)"
            proof -
              {
                assume a0: "i \<in> input_dist"
                have "i \<in> marg_input (makeDist s e)"
                proof -
                  {
                    have p0: "folds (\<lambda>t p. snd t + p) 0 (pmf (fst i) s e) = 1"
                      using \<open>s \<in> SN\<close> pmf_sum_one a0 by auto
                    obtain dw where a1: "dw = {t. \<exists>w \<in> (pmf (fst i) s e). t = ((fst i, fst w), snd i * snd w)}"
                      by auto
                    have p_dw: "{t. t \<in> makeDist s e \<and> fst (fst t) = fst i} = dw"
                      unfolding makeDist_def using a0 a1
                      by (smt Collect_cong fstI inputdist_unique mem_Collect_eq mult.commute)
                    have p1: "fst i \<in> (fst o fst) ` (makeDist s e)"
                      unfolding makeDist_def comp_def image_def using \<open>s \<in> SN\<close> a0 a1
                      by (smt eq_fst_iff equals0I fold_empty mem_Collect_eq pmf_sum_one)
                    have p2: "(fst i, folds (\<lambda>t p. snd t + p) 0 {d. d \<in> makeDist s e \<and> fst (fst d) = fst i}) \<in> marg_input (makeDist s e)"
                      unfolding marg_input_def using p1 by blast
                    have p3: "folds (\<lambda>t p. snd t + p) 0 {d. d \<in> makeDist s e \<and> fst (fst d) = fst i} =
                              folds (\<lambda>t p. snd t + p) 0 dw"
                      using p_dw p2 by auto
                    have p4: "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>w \<in> (pmf (fst i) s e). t = ((fst i, fst w), snd i * snd w)} =
                              folds (\<lambda>t p. snd t * snd i + p) 0 (pmf (fst i) s e)"
                      using folds_plus_times_output2[where ?w = "pmf (fst i) s e" and ?i = "i"] \<open>s \<in> SN\<close> a0 pmf_finite pmf_nonempty pmf_unique
                      by blast
                    have "folds (\<lambda>t p. snd t * snd i + p) 0 (pmf (fst i) s e) =
                          snd i * (folds (\<lambda>t p. snd t + p) 0 (pmf (fst i) s e))"
                      using folds_plus_times_output \<open>s \<in> SN\<close> a0 pmf_finite pmf_nonempty pmf_unique
                      by meson
                    then have p5: "folds (\<lambda>t p. snd t * snd i + p) 0 (pmf (fst i) s e) = snd i"
                      using p0 by auto
                    have "i \<in> marg_input (makeDist s e)"
                      using a1 p2 p3 p4 p5 by auto               
                  }
                  then show ?thesis by auto
                qed
              }
              then show ?thesis by auto
            qed
          }
          then show ?thesis by auto
        qed
      }
      then show ?thesis by auto
    qed

  lemma marg_input_sum_h2: "\<forall>s \<in> SN. \<forall>i e. i \<in> marg_input (makeDist s e) \<longrightarrow> i \<in> input_dist"
    by (smt CM.marg_input_sum_h1 CM_axioms fst_conv imageE makeDist_def marg_input_def mem_Collect_eq o_apply)

  lemma marg_input_sum_h3: "\<forall>e. \<forall>s \<in> SN. marg_input (makeDist s e) = input_dist"
    using marg_input_sum_h1 marg_input_sum_h2
    by blast

  lemma marg_input_sum: "\<forall>e. \<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (marg_input (makeDist s e)) = 1"
    using marg_input_sum_h3 inputdist_sum_one
    by simp

  lemma jodist_sum_one: "\<forall>e. \<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (makeDist s e) = 1"
    using jodist_marg_input_sum marg_input_sum
    by simp


  (*Output marginal probability distribution*)
  definition marg_output :: "(('i \<times> 'o) \<times> real) set \<Rightarrow> ('o \<times> real) set"
    where "marg_output jo_dist \<equiv> {t. \<exists>ou \<in> ((snd o fst) ` jo_dist).
                                     t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> jo_dist \<and> snd (fst d) = ou})}"

  lemma marg_output_finite:
    assumes a0: "finite (F::(('i \<times> 'o) \<times> real) set)"
        and a1: "F \<noteq> {}"
      shows "finite (marg_output F)"
    proof -
      show ?thesis using a0 a1
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        then show ?case
          unfolding marg_output_def by auto
      next
        case (insert x F)
        then show ?case
        proof(cases "snd (fst x) \<notin> (snd o fst) ` F")
          case True
          have p1: "(snd o fst) ` (insert x F) = {(snd (fst x))} \<union> ((snd o fst) ` F)"
            by auto
          then have p2: "marg_output (insert x F) = {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} \<union>
                                                    {t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
            unfolding marg_output_def by blast
          have "{d. d \<in> insert x F \<and> snd (fst d) = snd (fst x)} = {x}"
            using True by (smt Collect_cong comp_apply insertE insertI1 insert_image singleton_conv)
          then have p4: "{t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} = {(snd (fst x), snd x)}"
            by force
          have "\<forall>ou \<in> ((snd o fst) ` F). folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou} =
                                         folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou}"
            using True by (smt Collect_cong insert_iff)
          then have p5: "{t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} = marg_output F"
            unfolding marg_output_def by auto
          have "marg_output (insert x F) = (marg_output F) \<union> {(snd (fst x), snd x)}"
            using p2 p4 p5 by auto
          then show ?thesis
            by (simp add: insert.hyps(4)) 
        next
          case False
          then have p1: "(snd o fst) ` (insert x F) = ((snd o fst) ` F)"
            by (simp add: insert_absorb) 
          then have p2: "marg_output (insert x F) = {t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
            unfolding marg_output_def by auto
          have p3: "((snd o fst) ` F) = {(snd (fst x))} \<union> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}"
            using False by blast
          then have p4: "marg_output (insert x F) = 
                         {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} \<union>
                         {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
            using p2 by blast
          have c1: "\<forall>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. {d. d \<in> insert x F \<and> snd (fst d) = ou} = {d. d \<in> F \<and> snd (fst d) = ou}"
            by blast
          then have c2: "{t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} =
                         {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})}"
            by auto
          have "{t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})} \<subseteq> marg_output F"
            unfolding marg_output_def by blast
          then have c_final: "finite {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
            using c2 by (simp add: finite_subset insert.hyps(4))
          then show ?thesis
            using p4 by simp
        qed
      qed
    qed

  lemma marg_output_insert:
    assumes a0: "finite (F::(('i \<times> 'o) \<times> real) set)"
        and a1: "F \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> F \<and> j \<in> F \<longrightarrow> fst i \<noteq> fst j"
        and a3: "\<forall>d \<in> F. fst d \<noteq> fst x"
      shows "folds (\<lambda>t p. snd t + p) 0 (marg_output (insert x F)) = snd x + folds (\<lambda>t p. snd t + p) 0 (marg_output F)"
    proof -
      show ?thesis using a0 a1 a2 a3
      proof(cases "snd (fst x) \<notin> (snd o fst) ` F")
        case True
        have p1: "(snd o fst) ` (insert x F) = {(snd (fst x))} \<union> ((snd o fst) ` F)"
            by auto
        then have p2: "marg_output (insert x F) = {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} \<union>
                                                  {t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
          unfolding marg_output_def by blast
        have p3: "{t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} \<inter>
                  {t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} = {}"
          using True p1 by blast
        have "{d. d \<in> insert x F \<and> snd (fst d) = snd (fst x)} = {x}"
            using True by (smt Collect_cong comp_apply insertE insertI1 insert_image singleton_conv)
        then have p4: "{t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} = {(snd (fst x), snd x)}"
          by force
        have "\<forall>ou \<in> ((snd o fst) ` F). folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou} =
                                       folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou}"
          using True by (smt Collect_cong insert_iff)
        then have p5: "{t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} = marg_output F"
          unfolding marg_output_def by auto
        have "marg_output (insert x F) = (marg_output F) \<union> {(snd (fst x), snd x)}"
          using p2 p4 p5 by auto
        then have "folds (\<lambda>i p. snd i + p) 0 (marg_output (insert x F)) =
                   folds (\<lambda>i p. snd i + p) (folds (\<lambda>i p. snd i + p) 0 (marg_output F)) {(snd (fst x), snd x)}"
          using marg_output_finite a0 plus_comp_fun_commute_P.fold_set_union_disj[where ?P = "snd"]
          by (smt Int_commute a1 finite.emptyI finite.insertI p3 p4 p5)
        then have "folds (\<lambda>i p. snd i + p) 0 (marg_output (insert x F)) = snd x + folds (\<lambda>i p. snd i + p) 0 (marg_output F)"
          using plus_comp_fun_commute_P.fold_insert by simp
        then show ?thesis by auto
      next
        case False
        then have p1: "(snd o fst) ` (insert x F) = ((snd o fst) ` F)"
            by (simp add: insert_absorb) 
        then have p2: "marg_output (insert x F) = {t. \<exists>ou \<in> ((snd o fst) ` F). t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
          unfolding marg_output_def by auto
        have p3: "((snd o fst) ` F) = {(snd (fst x))} \<union> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}"
          using False by blast
        then have p4: "marg_output (insert x F) = 
                       {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} \<union>
                       {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
          using p2 by blast
        have p5: "finite (marg_output (insert x F))"
          by (simp add: a0 marg_output_finite)
        have p6_1: "finite {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}" 
          by auto
        have p6_2: "finite {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
          using p4 p5 by simp
        have p7: "{t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} \<inter>
                  {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} = {}"
          by auto
        have p8: "folds (\<lambda>i p. snd i + p) 0 (marg_output (insert x F)) =
                  folds (\<lambda>i p. snd i + p) (folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})})
                                          {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
          using plus_comp_fun_commute_P.fold_set_union_disj p4 p6_1 p6_2 p7 by simp 
        then have p9: "folds (\<lambda>i p. snd i + p) 0 (marg_output (insert x F)) =
                       folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} +
                       folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})}"
          by simp
        have b1: "{d. d \<in> insert x F \<and> snd (fst d) = snd (fst x)} = {x} \<union> {d. d \<in> F \<and> snd (fst d) = snd (fst x)}"
          by auto
        have b2: "{x} \<inter> {d. d \<in> F \<and> snd (fst d) = snd (fst x)} = {}"
          using a3 by fastforce
        have b3: "folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = snd (fst x)} =
                  folds (\<lambda>i p. snd i + p) (folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = snd (fst x)}) {x}"
          using plus_comp_fun_commute_P.fold_set_union_disj b1 b2
          by (simp add: Collect_conj_eq a0)
        then have b4: "folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = snd (fst x)} =
                       snd x + folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = snd (fst x)}"
          by simp
        then have b_final: "folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} =
                            snd x + folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = snd (fst x)}"
          by auto
        have c1: "\<forall>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. {d. d \<in> insert x F \<and> snd (fst d) = ou} = {d. d \<in> F \<and> snd (fst d) = ou}"
          by blast
        then have c_final: "folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> insert x F \<and> snd (fst d) = ou})} =
                            folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})}"
          by auto
        have d1: "marg_output F =
                  {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})} \<union>
                  {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})}"
          unfolding marg_output_def using p3 by blast
        have d2: "folds (\<lambda>i p. snd i + p) 0 (marg_output F) =
                  folds (\<lambda>i p. snd i + p) (folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})})
                                          {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})}"
          using plus_comp_fun_commute_P.fold_set_union_disj[where ?P = "snd"]
          by (smt Int_emptyI Un_commute a0 a1 d1 finite_Un fst_conv marg_output_finite mem_Collect_eq singletonD)
        then have d_final: "folds (\<lambda>i p. snd i + p) 0 (marg_output F) =
                            folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {e. e \<in> ((snd o fst) ` F) \<and> e \<noteq> snd (fst x)}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})} +
                            folds (\<lambda>i p. snd i + p) 0 {t. \<exists>ou \<in> {(snd (fst x))}. t = (ou, folds (\<lambda>i p. snd i + p) 0 {d. d \<in> F \<and> snd (fst d) = ou})}"
          by simp
        have "folds (\<lambda>i p. snd i + p) 0 (marg_output (insert x F)) = snd x + folds (\<lambda>i p. snd i + p) 0 (marg_output F)"
          using p9 b_final c_final d_final by simp
        then show ?thesis by auto
      qed
    qed

  lemma jodist_marg_output_induct:
    assumes a0: "finite (jodist::(('i \<times> 'o) \<times> real) set)"
        and a1: "jodist \<noteq> {}"
        and a2: "\<forall>i j. i \<noteq> j \<and> i \<in> jodist \<and> j \<in> jodist \<longrightarrow> fst i \<noteq> fst j"
      shows "folds (\<lambda>t p. snd t + p) 0 jodist =
             folds (\<lambda>t p. snd t + p) 0 (marg_output jodist)"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        have "folds (\<lambda>t p. snd t + p) 0 {x} = snd x"
          by auto
        moreover have "marg_output {x} = {(snd (fst x), snd x)}"
          unfolding marg_output_def comp_def
          by (smt Collect_cong calculation image_empty image_insert singletonI singleton_conv singleton_iff)
        ultimately have "folds (\<lambda>t p. snd t + p) 0 (marg_output {x}) = snd x"
          by auto
        then show ?case by auto
      next
        case (insert x F)
        have p1: "folds (\<lambda>t p. snd t + p) 0 (insert x F) = snd x + folds (\<lambda>t p. snd t + p) 0 F"
            using plus_comp_fun_commute_P.fold_insert insert.hyps(1) insert.hyps(3) by simp
        have p2: "folds (\<lambda>t p. snd t + p) 0 F = folds (\<lambda>t p. snd t + p) 0 (marg_output F)"
          using insert.hyps(4) insert.prems by blast
        moreover have "\<forall>d \<in> F. fst d \<noteq> fst x"
          using jodist_unique
          by (metis DiffD1 Diff_insert_absorb insert.hyps(3) insert.prems insertI1)
        moreover have "folds (\<lambda>t p. snd t + p) 0 (marg_output (insert x F)) = snd x + folds (\<lambda>t p. snd t + p) 0 (marg_output F)"
          using marg_output_insert
          by (metis DiffD1 Diff_insert_absorb calculation(2) insert.hyps(1) insert.hyps(2) insert.prems) 
        ultimately show ?case
          using p1 by linarith
      qed
    qed
  
  lemma jodist_marg_output_sum:
    "\<forall>e. \<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                  folds (\<lambda>t p. snd t + p) 0 (marg_output (makeDist s e))"
    proof -
      {
        fix e
        have "\<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                       folds (\<lambda>t p. snd t + p) 0 (marg_output (makeDist s e))"
        proof -
          {
            fix s
            assume "s \<in> SN"
            have "folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                  folds (\<lambda>t p. snd t + p) 0 (marg_output (makeDist s e))"
            proof -
              {
                have "finite (makeDist s e)"
                  using \<open>s \<in> SN\<close> jodist_finite by auto
                moreover have "makeDist s e \<noteq> {}"
                  using \<open>s \<in> SN\<close> jodist_nonempty by auto
                moreover have "\<forall>i j. i \<noteq> j \<and> i \<in> (makeDist s e) \<and> j \<in> (makeDist s e) \<longrightarrow> fst i \<noteq> fst j"
                  using \<open>s \<in> SN\<close> jodist_unique by blast
                ultimately show ?thesis
                  using jodist_marg_output_induct by blast
              }
            qed
          }
          then show ?thesis by blast
        qed
      }
      then show ?thesis by blast
    qed

  lemma marg_output_unique: "\<forall>e. \<forall>s \<in> SN. \<forall>d \<in> makeDist s e. \<exists>!t \<in> marg_output (makeDist s e). fst t = snd (fst d)"
    proof -
      {
        fix e
        have "\<forall>s \<in> SN. \<forall>d \<in> makeDist s e. \<exists>!t \<in> marg_output (makeDist s e). fst t = snd (fst d)"
        proof -
          {
            fix s
            assume "s \<in> SN"
            have "\<forall>d \<in> makeDist s e. \<exists>!t \<in> marg_output (makeDist s e). fst t = snd (fst d)"
            proof -
              {
                fix d
                assume "d \<in> makeDist s e"
                have "\<exists>!t \<in> marg_output (makeDist s e). fst t = snd (fst d)"
                proof -
                  {
                    have "snd (fst d) \<in> (snd o fst) ` (makeDist s e)"
                      using \<open>d \<in> makeDist s e\<close> unfolding makeDist_def by auto
                    then have "((snd (fst d)), folds (\<lambda>s p. snd s + p) 0 {u. u \<in> (makeDist s e) \<and> snd (fst u) = snd (fst d)}) \<in> marg_output (makeDist s e)"
                      using \<open>d \<in> makeDist s e\<close> unfolding marg_output_def by blast
                    then show ?thesis
                      using marg_output_def by auto
                  }
                qed
              }
              then show ?thesis by auto
            qed
          }
          then show ?thesis by auto
        qed
      }
      then show ?thesis by blast
    qed

  lemma marg_output_sum: "\<forall>e. \<forall>s \<in> SN. folds (\<lambda>t p. snd t + p) 0 (marg_output (makeDist s e)) = 1"
    using jodist_marg_output_sum jodist_sum_one
    by simp


  declare makeDist_def[cong] and marg_input_def[cong] and marg_output_def[cong]


subsection \<open>Information Flow Security Properties\<close>

  definition marg_times :: "('i \<times> real) set \<Rightarrow> ('o \<times> real) set \<Rightarrow> ('i \<times> 'o) \<Rightarrow> real"
    where "marg_times marg_i marg_o d \<equiv> let i = the_elem {t. t \<in> marg_i \<and> fst t = fst d};
                                            ou = the_elem {t. t \<in> marg_o \<and> fst t = snd d} in
                                        snd i * snd ou"

  definition mut_info :: "(('i \<times> 'o) \<times> real) set \<Rightarrow> real"
    where "mut_info jodist \<equiv> let marg_i = marg_input jodist;
                                 marg_o = marg_output jodist in
                                folds (\<lambda>t p. ((snd t) * log 2 ((snd t)/(marg_times marg_i marg_o (fst t)))) + p) 0 jodist"

  lemma folds_plus_zero:
    assumes a0: "finite (w::(('i \<times> 'o) \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>d \<in> w. P d = (0::real)"
      shows "folds (\<lambda>t p. P t + p) 0 w = 0"
    proof -
      {
        show ?thesis using a0 a1 a2
        proof(induct rule: finite_ne_induct)
          case (singleton x)
          have "folds (\<lambda>t p. P t + p) 0 {x} = P x + folds (\<lambda>t p. P t + p) 0 {}"
            using plus_comp_fun_commute_P.fold_insert by auto
          moreover have "folds (\<lambda>t p. P t + p) 0 {} = 0"
            by simp
          ultimately show ?case
            using a2 by (simp add: singleton.prems) 
        next
          case (insert x F)
          have "folds (\<lambda>t p. P t + p) 0 (insert x F) = P x + folds (\<lambda>t p. P t + p) 0 F"
            using plus_comp_fun_commute_P.fold_insert
            by (simp add: insert.hyps(1) insert.hyps(3))
          then show ?case
            by (simp add: insert.hyps(4) insert.prems) 
        qed
      }
    qed

  lemma folds_plus_positive:
    assumes a0: "finite (w::(('i \<times> 'o) \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i \<in> w. P i > (0::real)"
      shows "folds (\<lambda>s p. P s + p) 0 w > 0"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        then have "folds (\<lambda>s p. P s + p) 0 {x} = P x"
          by auto
        then show ?case
          using a2 by (simp add: singleton.prems) 
      next
        case (insert x F)
        have "folds (\<lambda>s p. P s + p) 0 (insert x F) = P x + folds (\<lambda>s p. P s + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert
          by (simp add: insert.hyps(1) insert.hyps(3)) 
        then show ?case
          by (simp add: insert.hyps(1) insert.hyps(3) insert.hyps(4) insert.prems pos_add_strict)
      qed
    qed

  lemma folds_plus_non_negative:
    assumes a0: "finite (w::(('i \<times> 'o) \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i \<in> w. P i \<ge> (0::real)"
      shows "folds (\<lambda>s p. P s + p) 0 w \<ge> 0"
    proof -
      show ?thesis using a0 a1 a2
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        then have "folds (\<lambda>s p. P s + p) 0 {x} = P x"
          by auto
        then show ?case
          using a2 by (simp add: singleton.prems) 
      next
        case (insert x F)
        have "folds (\<lambda>s p. P s + p) 0 (insert x F) = P x + folds (\<lambda>s p. P s + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert by (simp add: insert.hyps(1) insert.hyps(3))
        then show ?case
          using a2 insert.hyps(4) insert.prems by auto
      qed
    qed

  lemma folds_plus_non_negative2:
    assumes a0: "finite (w::(('i \<times> 'o) \<times> real) set)"
        and a1: "w \<noteq> {}"
        and a2: "\<forall>i \<in> w. P i \<ge> (0::real)"
        and a3: "d \<in> w"
        and a4: "P d > 0"
      shows "folds (\<lambda>s p. P s + p) 0 w > 0"
    proof -
      show ?thesis using a0 a1 a2 a3 a4
      proof(induct rule: finite_ne_induct)
        case (singleton x)
        then have "x = d"
          by blast
        then have "folds (\<lambda>s p. P s + p) 0 {d} = P d"
          by auto
        then show ?case
          using a4 by (simp add: \<open>x = d\<close>)
      next
        case (insert x F)
        have fold_insert: "folds (\<lambda>s p. P s + p) 0 (insert x F) = P x + folds (\<lambda>s p. P s + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert
          by (simp add: insert.hyps(1) insert.hyps(3))
        have "folds (\<lambda>s p. P s + p) 0 (insert x F) > 0"
          proof(cases "d = x")
            case True
            then have fold_insert_t: "folds (\<lambda>s p. P s + p) 0 (insert x F) = P d + folds (\<lambda>s p. P s + p) 0 F"
              using fold_insert by blast
            moreover have "folds (\<lambda>s p. P s + p) 0 F \<ge> 0"
              using folds_plus_non_negative
              by (simp add: insert.hyps(1) insert.hyps(2) insert.prems(1))
            ultimately show ?thesis
              using a4 by linarith
          next
            case False
            then have "d \<in> F"
              using insert.prems(2) by blast
            then show ?thesis
              using a4 fold_insert insert.hyps(4) insert.prems(1) by auto 
          qed
        then show ?case
          using a2 insert.hyps(4) insert.prems by auto 
      qed
    qed

  lemma folds_plus_value:
    assumes a_finite: "finite (w::(('i \<times> 'o) \<times> real) set)"
        and a_nonempty: "w \<noteq> {}"
        and a0: "\<forall>d \<in> w. P d = (i::real)"
      shows "folds (\<lambda>s p. P s + p) 0 w = i * card w"
    proof -
      show ?thesis using a_finite a_nonempty a0
      proof(induct arbitrary: i rule: finite_ne_induct)
        case (singleton x)
        then have "P x = i"
          by auto
        moreover have "folds (\<lambda>s p. P s + p) 0 {x} = P x"
          by force
        ultimately show ?case by auto
      next
        case (insert x F)
        have p0: "folds (\<lambda>s p. P s + p) 0 (insert x F) = P x + folds (\<lambda>s p. P s + p) 0 F"
          using plus_comp_fun_commute_P.fold_insert
          by (simp add: insert.hyps(1) insert.hyps(3)) 
        have p1: "folds (\<lambda>s p. P s + p) 0 F = i * card F"
          using insert.hyps(4) insert.prems by blast
        have p2: "P x + folds (\<lambda>s p. P s + p) 0 F = i * Suc (card F)"
          by (simp add: insert.prems p1 ring_class.ring_distribs(1))
        then show ?case using p0
          by (simp add: insert.hyps(1) insert.hyps(3)) 
      qed
    qed

  (* First Condition: W(o|i) = 0 *)

  definition pmf_zero :: "bool"
    where "pmf_zero \<equiv> \<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SE. \<forall>d \<in> pmf (fst i) s e. snd d = 0"

  lemma pmf_zero_makeDist:
    assumes pmf_zero: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SE. \<forall>d \<in> pmf (fst i) s e. snd d = 0"
    shows "\<forall>e. \<forall>s \<in> SE. \<forall>d \<in> makeDist s e. snd d = 0"
    unfolding makeDist_def using pmf_zero by auto

  lemma jodist_zero_mutinfo:
    assumes jodist_zero: "\<forall>e. \<forall>s \<in> SE. \<forall>d \<in> makeDist s e. snd d = 0"
      shows "\<forall>e. \<forall>s \<in> SE. mut_info (makeDist s e) = 0"
    proof -
      {
        show ?thesis using jodist_zero
        proof -
          {
            fix e
            have "\<forall>s \<in> SE. mut_info (makeDist s e) = 0"
            proof -
              {
                fix s
                assume "s \<in> SE"
                have "mut_info (makeDist s e) = 0"
                proof -
                  {
                    fix d
                    assume "d \<in> makeDist s e"
                    have "snd d = 0"
                      using \<open>d \<in> makeDist s e\<close> \<open>s \<in> SE\<close> jodist_zero by blast
                    then have "(snd d) * log 2 ((snd d)/(marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d))) = 0"
                      by simp
                    then have "\<forall>u \<in> makeDist s e. (snd u) * log 2 ((snd u)/(marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst u))) = 0"
                      using \<open>s \<in> SE\<close> jodist_zero mult_eq_0_iff by blast
                    then have "mut_info (makeDist s e) = 0"
                      unfolding mut_info_def Let_def using folds_plus_zero
                      proof -
                        have f1: "makeDist s e \<noteq> {}"
                          using \<open>d \<in> makeDist s e\<close> by blast
                        obtain pp :: "(('i \<times> 'o) \<times> real) set \<Rightarrow> (('i \<times> 'o) \<times> real \<Rightarrow> real) \<Rightarrow> ('i \<times> 'o) \<times> real" where
                          "\<And>P f. (infinite P \<or> pp P f \<in> P \<or> folds (\<lambda>p. (+) (f p)) 0 P = 0 \<or> P = {}) \<and> (infinite P \<or> f (pp P f) \<noteq> 0 \<or> folds (\<lambda>p. (+) (f p)) 0 P = 0 \<or> P = {})"
                          using \<open>\<And>w P. \<lbrakk>finite w; w \<noteq> {}; \<forall>d\<in>w. P d = 0\<rbrakk> \<Longrightarrow> folds (\<lambda>t. (+) (P t)) 0 w = 0\<close> by moura
                        then show "folds (\<lambda>p. (+) (snd p * log 2 (snd p / marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst p)))) 0 (makeDist s e) = 0"
                          using f1 by (meson \<open>\<forall>u\<in>makeDist s e. snd u * log 2 (snd u / marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst u)) = 0\<close> fold_infinite)
                      qed
                    then have ?thesis by auto
                  }
                  then show ?thesis
                    by (meson \<open>s \<in> SE\<close> equals0I jodist_nonempty state_subset subset_iff)
                qed
              }
              then show ?thesis by blast
            qed
          }
          then show ?thesis by auto
        qed
      }
    qed
  
  theorem condition_pmf_zero:
    assumes pmf_zero: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SE. \<forall>d \<in> pmf (fst i) s e. snd d = 0"
      shows "\<forall>e. \<forall>s \<in> SE. mut_info (makeDist s e) = 0"
    using pmf_zero_makeDist jodist_zero_mutinfo pmf_zero
    by blast

  (* Second Condition: W(o|i) = uniform *)

  definition pmf_uniform :: "bool"
    where "pmf_uniform \<equiv> \<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SE. \<forall>d \<in> pmf (fst i) s e. snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"

  lemma pmf_uniform_marg_tiems:
    assumes pmf_uniform: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SE. \<forall>d \<in> pmf (fst i) s e. snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
      shows "\<forall>e. \<forall>s \<in> SE. \<forall>d \<in> makeDist s e. marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd d"
    proof -
      {
        show ?thesis using pmf_uniform
        proof -
          {
            fix e
            have "\<forall>s \<in> SE. \<forall>d \<in> makeDist s e. marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd d"
            proof -
              {
                fix s
                assume  "s \<in> SE"
                then have "s \<in> SN" using state_subset by auto
                have "\<forall>d \<in> makeDist s e. marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd d"
                proof -
                  {
                    fix d
                    assume "d \<in> makeDist s e"
                    have "marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd d"
                    proof -
                      {
                        have "fst (fst d) \<in> fst ` input_dist"
                          using \<open>d \<in> makeDist s e\<close> unfolding makeDist_def by force
                        then have input_unique: "\<exists>!u \<in> input_dist. fst u = fst (fst d)"
                          using inputdist_unique by (metis (no_types, hide_lams) imageE) 
                        then obtain inputi where t0: "inputi \<in> input_dist \<and> fst inputi = fst (fst d)"
                          by auto
                        then have "folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> fst (fst u) = fst inputi} = snd inputi"
                          using marg_input_fold \<open>s \<in> SN\<close> by blast 
                        then have marg_input_sum: "folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> fst (fst u) = fst (fst d)} = snd inputi"
                          using t0 by auto
                        have margi_unique: "\<exists>!u. u \<in> marg_input (makeDist s e) \<and> fst u = fst (fst d)"
                          using marg_input_unique \<open>d \<in> makeDist s e\<close> \<open>s \<in> SN\<close> by blast
                        then obtain margi where a0: "margi \<in> marg_input (makeDist s e) \<and> fst margi = fst (fst d)"
                          by blast
                        have the_margi: "margi = the_elem {t. t \<in> marg_input (makeDist s e) \<and> fst t = fst (fst d)}"
                          unfolding the_elem_def using margi_unique a0
                          by (smt Collect_cong mem_Collect_eq singleton_conv2 the_equality)
                        have margi_value: "snd margi = snd inputi"
                          unfolding marg_input_def
                          using marg_input_sum a0 by auto
                        have margo_unique: "\<exists>!u. u \<in> marg_output (makeDist s e) \<and> fst u = snd (fst d)"
                          using marg_output_unique \<open>d \<in> makeDist s e\<close> \<open>s \<in> SN\<close> by blast
                        then obtain margo where b0: "margo \<in> marg_output (makeDist s e) \<and> fst margo = snd (fst d)"
                          by blast
                        have the_margo: "margo = the_elem {t. t \<in> marg_output (makeDist s e) \<and> fst t = snd (fst d)}"
                          unfolding the_elem_def using margo_unique b0
                          by (smt Collect_cong mem_Collect_eq singleton_conv2 the_equality)
                        have "snd margo = folds (\<lambda>s p. snd s + p) 0 {u. u \<in> (makeDist s e) \<and> snd (fst u) = snd (fst d)}"
                          unfolding marg_output_def using b0 by auto
                        then have "\<forall>i \<in> input_dist. \<forall>t \<in> pmf (fst i) s e. fst t = snd (fst d) \<longrightarrow> snd t = snd margo"
                          using pmf_uniform by (metis (no_types, lifting) Collect_cong \<open>s \<in> SE\<close>)
                        then have d_value: "snd d = snd inputi * snd margo"
                          using \<open>d \<in> makeDist s e\<close> unfolding makeDist_def
                          using input_unique t0 by force 
                        have "marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd inputi * snd margo"
                          using the_margi the_margo margi_value
                          unfolding marg_times_def Let_def the_elem_def by simp
                        then have ?thesis
                          using d_value by auto
                      }
                      then show ?thesis by blast
                    qed
                  }
                  then show ?thesis by blast
                qed
              }
              then show ?thesis by blast
            qed
          }
          then show ?thesis by blast
        qed
      }
    qed

  lemma marg_times_mutinfo:
    assumes marg_times_value: "\<forall>e. \<forall>s \<in> SE. \<forall>d \<in> makeDist s e. marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd d"
      shows "\<forall>e. \<forall>s \<in> SE. mut_info (makeDist s e) = 0"
    proof -
      {
        show ?thesis using marg_times_value
        proof -
          {
            fix e
            have "\<forall>s \<in> SE. mut_info (makeDist s e) = 0"
            proof -
              {
                fix s
                assume "s \<in> SE"
                then have "s \<in> SN" using state_subset by auto
                have "mut_info (makeDist s e) = 0"
                proof -
                  {
                    fix d
                    assume "d \<in> makeDist s e"
                    have "marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d) = snd d"
                      using \<open>d \<in> makeDist s e\<close> \<open>s \<in> SE\<close> marg_times_value by blast
                    then have "(snd d) * log 2 ((snd d)/(marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst d))) = 0"
                      by simp
                    then have "\<forall>u \<in> makeDist s e. (snd u) * log 2 ((snd u)/(marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst u))) = 0"
                      proof -
                        show ?thesis
                          by (metis \<open>s \<in> SE\<close> div_self log_one marg_times_value mult_eq_0_iff)
                      qed
                      then have "mut_info (makeDist s e) = 0"
                        unfolding mut_info_def Let_def using folds_plus_zero
                        proof -
                          have f1: "makeDist s e \<noteq> {}"
                            using \<open>d \<in> makeDist s e\<close> by blast
                          obtain pp :: "(('i \<times> 'o) \<times> real) set \<Rightarrow> (('i \<times> 'o) \<times> real \<Rightarrow> real) \<Rightarrow> ('i \<times> 'o) \<times> real" where
                            "\<And>P f. (infinite P \<or> pp P f \<in> P \<or> folds (\<lambda>p. (+) (f p)) 0 P = 0 \<or> P = {}) \<and> (infinite P \<or> f (pp P f) \<noteq> 0 \<or> folds (\<lambda>p. (+) (f p)) 0 P = 0 \<or> P = {})"
                            using \<open>\<And>w P. \<lbrakk>finite w; w \<noteq> {}; \<forall>d\<in>w. P d = 0\<rbrakk> \<Longrightarrow> folds (\<lambda>t. (+) (P t)) 0 w = 0\<close> by moura
                          then show "folds (\<lambda>p. (+) (snd p * log 2 (snd p / marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst p)))) 0 (makeDist s e) = 0"
                            using f1 by (meson \<open>\<forall>u\<in>makeDist s e. snd u * log 2 (snd u / marg_times (marg_input (makeDist s e)) (marg_output (makeDist s e)) (fst u)) = 0\<close> fold_infinite)
                        qed
                      then have ?thesis by auto
                    }
                    then show ?thesis
                      by (meson \<open>s \<in> SN\<close> equals0I jodist_nonempty)
                qed
              }
              then show ?thesis by blast
            qed
          }
          then show ?thesis by auto
        qed
      }
    qed

  theorem condition_pmf_uniform:
    assumes pmf_uniform: "\<forall>e. \<forall>i \<in> input_dist. \<forall>s \<in> SE. \<forall>d \<in> pmf (fst i) s e. snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
    shows "\<forall>e. \<forall>s \<in> SE. mut_info (makeDist s e) = 0"
    using pmf_uniform_marg_tiems marg_times_mutinfo pmf_uniform
    by blast


subsection \<open>Inference Framework of Information Flow Security Properties\<close>

  definition nonleakage :: "bool"
    where "nonleakage \<equiv> \<forall>e. \<forall>s \<in> SE. mut_info (makeDist s e) = 0"

  theorem pmf_zero_nonleakage:
    "pmf_zero \<Longrightarrow> nonleakage"
    using condition_pmf_zero nonleakage_def pmf_zero_def by blast 
  
  theorem pmf_uniform_nonleakage:
    "pmf_uniform \<Longrightarrow> nonleakage"
    using condition_pmf_uniform nonleakage_def pmf_uniform_def by blast 

end

end
