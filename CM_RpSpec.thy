section \<open>Random Permutation Cache\<close>

theory CM_RpSpec
  imports Main CM_SecurityModel
begin

subsection \<open>Data type, Basic components\<close>

(*Basic data structures*)
type_synonym tagmask = nat
type_synonym setbits = nat
type_synonym setindex = nat
type_synonym wayindex = nat

datatype cachehit = Hit | Miss

datatype secure = H | L

datatype event = RP_READ | RP_WRITE

(*Memory blocks*)
record memory_request =
  tag :: tagmask
  index :: setbits
  protect :: bool
  thread :: secure

(*Cache structure*)
record cache_line =
  ca_tag :: tagmask
  ca_set :: setindex
  ca_way :: wayindex
  valid :: bool
  lock :: bool
  owned :: "secure option"

type_synonym cache = "(cache_line set) list"

type_synonym mapping = "setbits \<rightharpoonup> setindex"

(*State Machine*)
record state =
  sram :: cache
  map_H :: mapping
  map_L :: mapping

subsection \<open>Random permutation cache model specifications\<close>

definition replace_policy :: "cache_line set \<Rightarrow> cache_line"
  where "replace_policy cs \<equiv> SOME l. l \<in> cs"

definition probe_line :: "cache_line set \<Rightarrow> memory_request \<Rightarrow> bool"
  where "probe_line cs mr \<equiv> \<exists>b. b \<in> cs \<and> ca_tag b = tag mr \<and> valid b \<and> owned b = Some (thread mr)"

definition replace_line :: "cache_line \<Rightarrow> memory_request \<Rightarrow> cache_line"
  where "replace_line cl mr \<equiv> cl\<lparr>ca_tag := tag mr, valid := True, lock := protect mr, owned := Some (thread mr)\<rparr>"

definition drop_line :: "cache_line \<Rightarrow> cache_line"
  where "drop_line cl \<equiv> cl\<lparr>valid := False, lock := False, owned := None\<rparr>"

definition fix_line :: "cache_line set \<Rightarrow> memory_request \<Rightarrow> cache_line set"
  where "fix_line cs mr \<equiv> {t. \<exists>r \<in> cs. t = (if owned r = Some (thread mr) then r\<lparr>valid := False, lock := False, owned := None\<rparr> else r)}"

definition swap_map :: "mapping \<Rightarrow> setindex \<Rightarrow> setindex \<Rightarrow> mapping"
  where "swap_map pt ra rb \<equiv> let sa = {t. pt t = Some ra}; sb = {t. pt t = Some rb} in
                             (\<lambda>t. if t \<in> sa then Some rb else if t \<in> sb then Some ra else pt t)"

definition rp_read :: "state \<Rightarrow> memory_request \<Rightarrow> state set" where
  "rp_read s mr \<equiv>
      let map = (if thread mr = H then map_H s else map_L s);
          redir_set = the (map (index mr));
          redir_ca = (sram s) ! redir_set in
      if probe_line redir_ca mr then {s}
      else let r_line = replace_policy redir_ca;
               policy_line = {t. \<exists>l \<in> {0..length (sram s) - 1}. t = replace_policy ((sram s) ! l)} in
        if owned r_line = Some (thread mr) then
          if lock r_line = protect mr then
            let newset = insert (replace_line r_line mr) (redir_ca - {r_line}) in
            {s\<lparr>sram := list_update (sram s) redir_set newset\<rparr>}
          else {t. \<exists>r'_line \<in> policy_line. let newset = insert (drop_line r'_line) (((sram s) ! (ca_set r'_line)) - {r'_line}) in
                   t = s\<lparr>sram := list_update (sram s) (ca_set r'_line) newset\<rparr>}
        else
          if thread mr = H then
            {t. \<exists>r'_line \<in> policy_line.
              if ca_set r'_line = redir_set then
                let newset = insert (replace_line r'_line mr) (fix_line (((sram s) ! (ca_set r'_line)) - {r'_line}) mr) in
                    t = s\<lparr>sram := list_update (sram s) (ca_set r'_line) newset,
                          map_H := swap_map (map_H s) redir_set (ca_set r'_line)\<rparr>
              else let newset = insert (replace_line r'_line mr) (fix_line (((sram s) ! (ca_set r'_line)) - {r'_line}) mr);
                       new_redir_ca = fix_line redir_ca mr in
                t = s\<lparr>sram := list_update (list_update (sram s) (ca_set r'_line) newset) redir_set new_redir_ca,
                      map_H := swap_map (map_H s) redir_set (ca_set r'_line)\<rparr>}
          else {t. \<exists>r'_line \<in> policy_line.
                 if ca_set r'_line = redir_set then
                   let newset = insert (replace_line r'_line mr) (fix_line (((sram s) ! (ca_set r'_line)) - {r'_line}) mr) in
                       t = s\<lparr>sram := list_update (sram s) (ca_set r'_line) newset,
                             map_L := swap_map (map_L s) redir_set (ca_set r'_line)\<rparr>
                 else let newset = insert (replace_line r'_line mr) (fix_line (((sram s) ! (ca_set r'_line)) - {r'_line}) mr);
                          new_redir_ca = fix_line redir_ca mr in
                   t = s\<lparr>sram := list_update (list_update (sram s) (ca_set r'_line) newset) redir_set new_redir_ca,
                         map_L := swap_map (map_L s) redir_set (ca_set r'_line)\<rparr>}"


subsection \<open>Instantiation\<close>

record cache_NE =
  ca_N :: "cache set"
  ca_E :: "cache set"

consts cache_comp :: cache_NE

definition cache_comp_witness :: "cache_NE"
  where "cache_comp_witness \<equiv> \<lparr>ca_N = {[{(\<lparr>ca_tag = 0, ca_set = 0, ca_way = 0, valid = True, lock = False, owned = Some L\<rparr>)}]},
                               ca_E = {[{(\<lparr>ca_tag = 0, ca_set = 0, ca_way = 0, valid = True, lock = False, owned = Some L\<rparr>)}]}\<rparr>"

specification (cache_comp)
  caN_finite: "finite (ca_N cache_comp)"
  caN_nonempty: "(ca_N cache_comp) \<noteq> {}"

  ca_length: "\<forall>c \<in> (ca_N cache_comp). length c > 0"
  ca_length2: "\<forall>c1 c2. c1 \<in> (ca_N cache_comp) \<and> c2 \<in> (ca_N cache_comp) \<and> c1 \<noteq> c2 \<longrightarrow> length c1 = length c2"
  ca_finite: "\<forall>c \<in> (ca_N cache_comp). finite (set c)"
  ca_set_nonempty: "\<forall>c \<in> (ca_N cache_comp). (\<forall>l < length c. c!l \<noteq> {})"
  ca_set_finite: "\<forall>c \<in> (ca_N cache_comp). (\<forall>l < length c. finite (c!l))"
  ca_set_num: "\<forall>c \<in> (ca_N cache_comp). (\<forall>l < length c. \<forall>e \<in> (c!l). ca_set e = l)"
  ca_way_num: "\<forall>c \<in> (ca_N cache_comp). (\<forall>l1 l2. l1 < length c \<and> l2 < length c \<and> l1 \<noteq> l2 \<longrightarrow> card(c!l1) = card(c!l2))"
  ca_way_num2: "\<forall>c \<in> (ca_N cache_comp). (\<forall>l < length c. \<forall>e1 e2. e1 \<in> (c!l) \<and> e2 \<in> (c!l) \<and> e1 \<noteq> e2 \<longrightarrow> ca_way e1 \<noteq> ca_way e2)"

  caE_init: "(ca_E cache_comp) \<subseteq> (ca_N cache_comp)"
  caE_nonempty: "(ca_E cache_comp) \<noteq> {}"
  caE_occupy: "\<forall>c \<in> (ca_E cache_comp). (\<forall>l < length c. \<forall>e \<in> (c!l). owned e = Some L)"
  apply(intro exI[of _ cache_comp_witness])
  unfolding cache_comp_witness_def by auto

record mem_map =
  map_conf :: "mapping"
  mem_req :: "(memory_request \<times> real) set"

consts mm_comp :: mem_map

definition mm_comp_witness :: "mem_map"
  where "mm_comp_witness \<equiv> \<lparr>map_conf = (\<lambda>t. if t = 0 then Some 0 else None),
                            mem_req = {(\<lparr>tag = 0, index = 0, protect = False, thread = H\<rparr>, 1)}\<rparr>"

specification (mm_comp)
  map_range: "\<forall>c \<in> (ca_N cache_comp). (\<forall>i. (map_conf mm_comp) i \<noteq> None \<longrightarrow> the ((map_conf mm_comp) i) < length c)"
  map_diff: "\<forall>i j. i \<noteq> j \<and> (map_conf mm_comp) i \<noteq> None \<and> (map_conf mm_comp) j \<noteq> None \<longrightarrow> the ((map_conf mm_comp) i) \<noteq> the ((map_conf mm_comp) j)"
  mem_finite: "finite (mem_req mm_comp)"
  mem_nonempty: "card (mem_req mm_comp) > 0"
  mem_unique: "\<forall>i j. i \<in> (mem_req mm_comp) \<and> j \<in> (mem_req mm_comp) \<and> i \<noteq> j \<longrightarrow> index (fst i) \<noteq> index (fst j)"
  mem_positive: "\<forall>i \<in> (mem_req mm_comp). snd i > 0"
  mem_sum_one: "folds (\<lambda>t p. snd t + p) 0 (mem_req mm_comp) = 1"
  mem_occupy: "\<forall>i \<in> (mem_req mm_comp). thread (fst i) = H"
  mem_mapping: "\<forall>i \<in> (mem_req mm_comp). (map_conf mm_comp) (index (fst i)) \<noteq> None"
  apply(intro exI[of _ "mm_comp_witness"])
  unfolding mm_comp_witness_def apply auto
  using ca_length by auto

(*state N*)
consts state_N :: "state set"

definition state_N_witness :: "state set"
  where "state_N_witness \<equiv> {t. \<exists>c \<in> (ca_N cache_comp). t = \<lparr>sram = c, map_H = (map_conf mm_comp), map_L = (map_conf mm_comp)\<rparr>}"

specification (state_N)
  state_N_init: "state_N = state_N_witness"
  by simp

lemma stateN_finite: "finite state_N"
  proof -
    {
      have "\<forall>c \<in> (ca_N cache_comp). finite {t. \<exists>c \<in> (ca_N cache_comp). t = \<lparr>sram = c, map_H = (map_conf mm_comp), map_L = (map_conf mm_comp)\<rparr>}"
        using caN_finite by auto
      then show ?thesis
        using state_N_init state_N_witness_def by auto 
    }
  qed

lemma stateN_nonempty: "state_N \<noteq> {}"
  using state_N_init state_N_witness_def caN_nonempty
  by blast

(*state E*)
consts state_E :: "state set"

definition state_E_witness :: "state set"
  where "state_E_witness \<equiv> {t. \<exists>c \<in> (ca_E cache_comp). t = \<lparr>sram = c, map_H = (map_conf mm_comp), map_L = (map_conf mm_comp)\<rparr>}"

specification (state_E)
  state_E_init: "state_E = state_E_witness"
  by simp

lemma stateE_nonempty: "state_E \<noteq> {}"
  using state_E_init state_E_witness_def caE_nonempty
  by blast

lemma stateE_subset: "state_E \<subseteq> state_N"
  using state_N_init state_N_witness_def state_E_init state_E_witness_def
  by (smt Collect_mono_iff caE_init subset_eq)
  
lemma cache_set_size:
  "\<forall>s \<in> state_N. card {0..length (sram s) - 1} = length (sram s)"
  proof -
    {
      fix s
      assume "s \<in> state_N"
      have "card {0..length (sram s) - 1} = length (sram s)"
      proof -
        {
          have "sram s \<in> ca_N cache_comp"
            using state_N_init unfolding state_N_witness_def
            proof -
              assume "state_N = {t. \<exists>c\<in>ca_N cache_comp. t = \<lparr>sram = c, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
              then have "state_N = {s. \<exists>Cs. Cs \<in> ca_N cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
                by meson
              then have "\<exists>Cs. Cs \<in> ca_N cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>"
                using \<open>s \<in> state_N\<close> by blast
              then show ?thesis
                by force
            qed
          then show ?thesis
            using ca_length by simp
        }
      qed
    }
    then show ?thesis by auto
  qed
  
lemma cache_set_size2:
  assumes a_finite: "finite (w::((nat \<times> cachehit) \<times> real) set)"
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

lemma policy_line_length:
  assumes a0: "finite A"
      and a1: "A \<noteq> {}"
      and a2: "\<forall>a1 a2. a1 \<in> A \<and> a2 \<in> A \<and> a1 \<noteq> a2 \<longrightarrow> f a1 \<noteq> f a2"
    shows "card {t. \<exists>a \<in> A. t = f a} = card A"
  proof -
    show ?thesis using a0 a1 a2
    proof(induct rule: finite_ne_induct)
      case (singleton x)
      then show ?case by auto
    next
      case (insert x F)
      have insert_length: "card (insert x F) = card F + 1"
        by (simp add: insert.hyps(1) insert.hyps(3))
      have "{t. \<exists>a \<in> (insert x F). t = f a} = {t. \<exists>a \<in> {x}. t = f a} \<union> {t. \<exists>a \<in> F. t = f a}"
        by auto
      moreover have "f x \<notin> {t. \<exists>a \<in> F. t = f a}"
        using insert.hyps(3) insert.prems by blast
      ultimately have "card {t. \<exists>a \<in> (insert x F). t = f a} = card {t. \<exists>a \<in> F. t = f a} + 1"
        using insert.hyps(1) by auto
      then show ?case
        using insert_length by (simp add: insert.hyps(4) insert.prems) 
    qed
  qed

(*Observation*)
definition rp_read_observe :: "state \<Rightarrow> memory_request \<Rightarrow> ((setindex \<times> cachehit) \<times> real) set" where
  "rp_read_observe s mr \<equiv>
      let maps = map_H s;
          redir_set = the (maps (index mr));
          redir_ca = (sram s) ! redir_set in
      if probe_line redir_ca mr then {((redir_set, Hit), 1)}
      else let r_line = replace_policy redir_ca;
               policy_line = {t. \<exists>l \<in> {0..length (sram s) - 1}. t = replace_policy ((sram s) ! l)} in
        if owned r_line = Some (thread mr) then
          if lock r_line = protect mr then {((redir_set, Miss), 1)}
          else {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)}
        else
          {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)}"

lemma mem_cache_miss:
  "\<forall>i \<in> mem_req mm_comp. \<forall>s0 \<in> state_E. rp_read_observe s0 (fst i) = {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
  proof -
    {
      fix i
      assume t0: "i \<in> mem_req mm_comp"
      have "\<forall>s0 \<in> state_E. rp_read_observe s0 (fst i) = {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
      proof -
        {
          fix s0
          assume t00: "s0 \<in> state_E"
          have "rp_read_observe s0 (fst i) = {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
          proof -
            {
              have iowned: "thread (fst i) = H"
                by (simp add: mem_occupy t0)
              let ?maps = "map_H s0"
              let ?redir_set = "the (?maps (index (fst i)))"
              have exi_redir: "?redir_set < length (sram s0)"
                using state_E_init unfolding state_E_witness_def using mem_mapping
                by (smt caE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t00)
              let ?redir_ca = "(sram s0) ! ?redir_set"
              have t000: "sram s0 \<in> ca_E cache_comp"
                using state_E_init unfolding state_E_witness_def
                proof -
                  assume "state_E = {t. \<exists>c\<in>ca_E cache_comp. t = \<lparr>sram = c, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
                  then have "state_E = {s. \<exists>Cs. Cs \<in> ca_E cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
                    by meson
                  then have "\<exists>Cs. Cs \<in> ca_E cache_comp \<and> s0 = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>"
                    using t00 by blast
                  then show ?thesis
                    by fastforce
                qed
              then have setowned: "\<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). owned e = Some L"
                using caE_occupy by blast
              then have "\<nexists>b. b \<in> ?redir_ca \<and> ca_tag b = tag (fst i) \<and> valid b \<and> owned b = Some (thread (fst i))"
                using iowned exi_redir by auto
              then have c1: "\<not> probe_line ?redir_ca (fst i)"
                unfolding probe_line_def by blast
              let ?r_line = "replace_policy ?redir_ca"
              have "?r_line \<in> ?redir_ca"
                unfolding replace_policy_def
                using caE_init ca_set_nonempty some_in_eq t000 exi_redir by blast
              then have "owned ?r_line = Some L"
                using setowned exi_redir by blast
              then have c2: "owned ?r_line \<noteq> Some (thread (fst i))"
                using iowned by auto
              let ?policy_line = "{t. \<exists>l \<in> {0..length (sram s0) - 1}. t = replace_policy ((sram s0) ! l)}"
              have out: "rp_read_observe s0 (fst i) = {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/card ?policy_line)}"
                unfolding rp_read_observe_def Let_def
                using c1 c2 by (simp add: iowned)
              have length_finite: "finite {0..length (sram s0) - 1}"
                by blast
              have length_nonempty: "{0..length (sram s0) - 1} \<noteq> {}"
                using atLeastatMost_empty_iff by blast
              have caset_line: "\<forall>l \<in> {0..length (sram s0) - 1}. ca_set (replace_policy ((sram s0) ! l)) = l"
                unfolding replace_policy_def
                proof -
                  { 
                    fix nn :: nat
                    have "sram s0 \<in> ca_N cache_comp"
                      using caE_init t000 by blast
                    then have "nn \<notin> {0..length (sram s0) - 1} \<or> ca_set (SOME c. c \<in> sram s0 ! nn) = nn"
                      by (metis (no_types) Suc_pred' atLeastAtMost_iff atLeastatMost_empty_iff2 ca_length ca_set_nonempty ca_set_num card_0_eq card_atLeastAtMost finite_atLeastAtMost neq0_conv some_in_eq zero_less_diff) 
                  }
                  then show "\<forall>n\<in>{0..length (sram s0) - 1}. ca_set (SOME c. c \<in> sram s0 ! n) = n"
                    by blast
                qed
              then have line_diff: "\<forall>l1 l2. l1 \<in> {0..length (sram s0) - 1} \<and> l2 \<in> {0..length (sram s0) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                                    (replace_policy ((sram s0) ! l1)) \<noteq> (replace_policy ((sram s0) ! l2))"
                proof -
                  show ?thesis
                    by (metis (no_types) caset_line)
                qed
              have policy_length: "card ?policy_line = card {0..length (sram s0) - 1}"
                using length_finite length_nonempty line_diff
                by (simp add: policy_line_length)
              then have policy_length2: "card ?policy_line = length (sram s0)"
                using cache_set_size t00 stateE_subset by auto
              then have out1: "{t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/card ?policy_line)} =
                               {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}"  
                by auto
              have s1: "\<forall>e \<in> {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}.
                         e \<in> {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
                proof -
                  {
                    fix e
                    assume e0: "e \<in> {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}"
                    have "fst (fst e) \<in> {0..length (sram s0) - 1}"
                      using e0 caset_line by auto
                    then have "\<exists>d \<in> {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}. d = e"
                      using e0 by auto
                    then have "e \<in> {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
                      by auto
                  }
                  then show ?thesis by blast
                qed
              have s2: "\<forall>e \<in> {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}.
                         e \<in> {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}"
                proof -
                  {
                    fix e
                    assume e1: "e \<in> {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
                    have "fst (fst e) \<in> {0..length (sram s0) - 1}"
                      using e1 by auto
                    moreover have "\<forall>d \<in> {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}. fst (fst d) \<in> {0..length (sram s0) - 1}"
                      using caset_line by auto
                    ultimately have "\<exists>d \<in> {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}. d = e"
                      by (smt caset_line e1 mem_Collect_eq)
                    then have "e \<in> {t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))}"
                      by auto
                  }
                  then show ?thesis by blast
                qed
              have out_equal: "{t. \<exists>r'_line \<in> ?policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s0))} =
                               {t. \<exists>r \<in> {0..length (sram s0) - 1}. t = ((r, Miss), 1/length (sram s0))}"
                using s1 s2 by blast 
              show ?thesis
                using out out_equal policy_length2 by presburger
            }
          qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed

(*pmf instantiate*)
definition execution :: "memory_request \<Rightarrow> state \<Rightarrow> event \<Rightarrow> ((setindex \<times> cachehit) \<times> real) set"
  where "execution mr s e \<equiv> rp_read_observe s mr"

lemma read_finite:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. finite (execution (fst mr) s e)"
  unfolding execution_def rp_read_observe_def Let_def
  by simp

lemma read_nonempty_h1:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "probe_line redir_ca (fst mr)"
    shows "execution (fst mr) s e \<noteq> {}"
  unfolding execution_def rp_read_observe_def Let_def
  using t0 a0 a1 a2 a3 by auto

lemma read_nonempty_h2:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "owned r_line = Some (thread (fst mr))"
      and a6: "lock r_line = protect (fst mr)"
    shows "execution (fst mr) s e \<noteq> {}"
  unfolding execution_def rp_read_observe_def Let_def
    using t0 a0 a1 a2 a3 a4 a5 a6 by auto

lemma read_nonempty_h3:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "policy_line = {t. \<exists>l \<in> {0..length (sram s) - 1}. t = replace_policy ((sram s) ! l)}"
      and a6: "owned r_line = Some (thread (fst mr))"
      and a7: "lock r_line \<noteq> protect (fst mr)"
    shows "execution (fst mr) s e \<noteq> {}"
  proof -
    {
      have exi_redir: "redir_set < length (sram s)"
        using state_N_init unfolding state_N_witness_def using mem_mapping
        by (smt a0 a1 map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
      have out: "execution (fst mr) s e = {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)}"
        unfolding execution_def rp_read_observe_def Let_def
        using t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 by auto
      have length_finite: "finite {0..length (sram s) - 1}"
        by blast
      have length_nonempty: "{0..length (sram s) - 1} \<noteq> {}"
        using atLeastatMost_empty_iff by blast
      have caset_line: "\<forall>l \<in> {0..length (sram s) - 1}. ca_set (replace_policy ((sram s) ! l)) = l"
        unfolding replace_policy_def
        proof -
          { 
            fix nn :: nat
            have "sram s \<in> ca_N cache_comp"
              by (smt mem_Collect_eq state.select_convs(1) state_N_init state_N_witness_def t0)
            then have "nn \<notin> {0..length (sram s) - 1} \<or> ca_set (SOME c. c \<in> sram s ! nn) = nn"
              by (metis (no_types) Suc_pred' atLeastAtMost_iff atLeastatMost_empty_iff2 ca_length ca_set_nonempty ca_set_num card_0_eq card_atLeastAtMost finite_atLeastAtMost neq0_conv some_in_eq zero_less_diff) 
          }
          then show "\<forall>n\<in>{0..length (sram s) - 1}. ca_set (SOME c. c \<in> sram s ! n) = n"
            by blast
        qed
      then have line_diff: "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                            (replace_policy ((sram s) ! l1)) \<noteq> (replace_policy ((sram s) ! l2))"
        proof -
          show ?thesis
            by (metis (no_types) caset_line)
        qed
      have policy_length: "card policy_line = card {0..length (sram s) - 1}"
        using length_finite length_nonempty line_diff a5
        by (simp add: policy_line_length)
      then have policy_length2: "card policy_line = length (sram s)"
        using cache_set_size t0 by auto
      then have out1: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)} =
                       {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        by auto
      have s1: "\<forall>e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e0: "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e0 caset_line a5 by auto
            then have "\<exists>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. d = e"
              using e0 by auto
            then have "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have s2: "\<forall>e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e1: "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e1 by auto
            moreover have "\<forall>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. fst (fst d) \<in> {0..length (sram s) - 1}"
              using caset_line a5 by auto
            ultimately have "\<exists>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. d = e"
              by (smt caset_line e1 a5 mem_Collect_eq)
            then have "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have out_equal: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))} =
                       {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using s1 s2 by blast
      then have out2: "execution (fst mr) s e = {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using out out1 by auto
      have finite_out: "finite {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        by auto
      have nonempty_out: "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} \<noteq> {}"
        by auto
      have value_out: "\<forall>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. snd d = 1/length (sram s)"
        by auto
      have "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} =
           1/length (sram s) * card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using cache_set_size2[where ?w = "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}" and
                                    ?P = "snd" and
                                    ?i = "1/length (sram s)"]
              finite_out nonempty_out value_out by blast
      moreover have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} = length (sram s)"
      proof -
        {
          have "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                ((l1, Miss), 1/length (sram s)) \<noteq> ((l2, Miss), 1/length (sram s))"
            by auto
          then have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1 / real (length (sram s)))} =
                     card {0..length (sram s) - 1}"
            using length_finite length_nonempty
            by (simp add: policy_line_length)
          then show ?thesis
            using cache_set_size t0 by auto
        }
      qed
      ultimately show ?thesis
        using of_nat_0 out2 by force 
    }
  qed

lemma read_nonempty_h4:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "policy_line = {t. \<exists>l \<in> {0..length (sram s) - 1}. t = replace_policy ((sram s) ! l)}"
      and a6: "owned r_line \<noteq> Some (thread (fst mr))"
    shows "execution (fst mr) s e \<noteq> {}"
  proof -
    {
      have exi_redir: "redir_set < length (sram s)"
        using state_N_init unfolding state_N_witness_def using mem_mapping
        by (smt a0 a1 map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
      have out: "execution (fst mr) s e = {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)}"
        unfolding execution_def rp_read_observe_def Let_def
        using t0 t1 a0 a1 a2 a3 a4 a5 a6 by auto
      have length_finite: "finite {0..length (sram s) - 1}"
        by blast
      have length_nonempty: "{0..length (sram s) - 1} \<noteq> {}"
        using atLeastatMost_empty_iff by blast
      have caset_line: "\<forall>l \<in> {0..length (sram s) - 1}. ca_set (replace_policy ((sram s) ! l)) = l"
        unfolding replace_policy_def
        proof -
          { 
            fix nn :: nat
            have "sram s \<in> ca_N cache_comp"
              by (smt mem_Collect_eq state.select_convs(1) state_N_init state_N_witness_def t0)
            then have "nn \<notin> {0..length (sram s) - 1} \<or> ca_set (SOME c. c \<in> sram s ! nn) = nn"
              by (metis (no_types) Suc_pred' atLeastAtMost_iff atLeastatMost_empty_iff2 ca_length ca_set_nonempty ca_set_num card_0_eq card_atLeastAtMost finite_atLeastAtMost neq0_conv some_in_eq zero_less_diff) 
          }
          then show "\<forall>n\<in>{0..length (sram s) - 1}. ca_set (SOME c. c \<in> sram s ! n) = n"
            by blast
        qed
      then have line_diff: "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                            (replace_policy ((sram s) ! l1)) \<noteq> (replace_policy ((sram s) ! l2))"
        proof -
          show ?thesis
            by (metis (no_types) caset_line)
        qed
      have policy_length: "card policy_line = card {0..length (sram s) - 1}"
        using length_finite length_nonempty line_diff a5
        by (simp add: policy_line_length)
      then have policy_length2: "card policy_line = length (sram s)"
        using cache_set_size t0 by auto
      then have out1: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)} =
                       {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        by auto
      have s1: "\<forall>e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e0: "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e0 caset_line a5 by auto
            then have "\<exists>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. d = e"
              using e0 by auto
            then have "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have s2: "\<forall>e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e1: "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e1 by auto
            moreover have "\<forall>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. fst (fst d) \<in> {0..length (sram s) - 1}"
              using caset_line a5 by auto
            ultimately have "\<exists>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. d = e"
              by (smt caset_line e1 a5 mem_Collect_eq)
            then have "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have out_equal: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))} =
                       {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using s1 s2 by blast
      then have out2: "execution (fst mr) s e = {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using out out1 by auto
      have finite_out: "finite {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        by auto
      have nonempty_out: "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} \<noteq> {}"
        by auto
      have value_out: "\<forall>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. snd d = 1/length (sram s)"
        by auto
      have "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} =
           1/length (sram s) * card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using cache_set_size2[where ?w = "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}" and
                                    ?P = "snd" and
                                    ?i = "1/length (sram s)"]
              finite_out nonempty_out value_out by blast
      moreover have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} = length (sram s)"
      proof -
        {
          have "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                ((l1, Miss), 1/length (sram s)) \<noteq> ((l2, Miss), 1/length (sram s))"
            by auto
          then have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1 / real (length (sram s)))} =
                     card {0..length (sram s) - 1}"
            using length_finite length_nonempty
            by (simp add: policy_line_length)
          then show ?thesis
            using cache_set_size t0 by auto
        }
      qed
      ultimately show ?thesis
        using of_nat_0 out2 by force 
    }
  qed

lemma read_nonempty:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. execution (fst mr) s e \<noteq> {}"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. execution (fst mr) s e \<noteq> {}"
      proof -
        {
          fix mr
          assume t0: "mr \<in> mem_req mm_comp"
          have "\<forall>s \<in> state_N. execution (fst mr) s e \<noteq> {}"
          proof -
            {
              fix s
              assume t1: "s \<in> state_N"
              have "execution (fst mr) s e \<noteq> {}"
                using read_nonempty_h1 read_nonempty_h2 read_nonempty_h3 read_nonempty_h4 t0 t1
                by meson 
            }
            then show ?thesis by blast
          qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed

lemma read_unique:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. \<forall>m n. m \<in> (execution (fst mr) s e) \<and> n \<in> (execution (fst mr) s e) \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n"
  unfolding execution_def rp_read_observe_def Let_def
  by auto

lemma read_positive:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. \<forall>d \<in> (execution (fst mr) s e). snd d \<ge> 0"
  unfolding execution_def rp_read_observe_def Let_def
  by (smt mem_Collect_eq of_nat_0_le_iff singletonD snd_conv zero_le_divide_1_iff)

lemma read_sum_one_h1:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "probe_line redir_ca (fst mr)"
    shows "folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  unfolding execution_def rp_read_observe_def Let_def
  using t0 a0 a1 a2 a3 by auto

lemma read_sum_one_h2:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "owned r_line = Some (thread (fst mr))"
      and a6: "lock r_line = protect (fst mr)"
    shows "folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  unfolding execution_def rp_read_observe_def Let_def
    using t0 a0 a1 a2 a3 a4 a5 a6 by auto

lemma read_sum_one_h3:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "policy_line = {t. \<exists>l \<in> {0..length (sram s) - 1}. t = replace_policy ((sram s) ! l)}"
      and a6: "owned r_line = Some (thread (fst mr))"
      and a7: "lock r_line \<noteq> protect (fst mr)"
    shows "folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  proof -
    {
      have exi_redir: "redir_set < length (sram s)"
        using state_N_init unfolding state_N_witness_def using mem_mapping
        by (smt a0 a1 map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
      have out: "execution (fst mr) s e = {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)}"
        unfolding execution_def rp_read_observe_def Let_def
        using t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 by auto
      have length_finite: "finite {0..length (sram s) - 1}"
        by blast
      have length_nonempty: "{0..length (sram s) - 1} \<noteq> {}"
        using atLeastatMost_empty_iff by blast
      have caset_line: "\<forall>l \<in> {0..length (sram s) - 1}. ca_set (replace_policy ((sram s) ! l)) = l"
        unfolding replace_policy_def
        proof -
          { 
            fix nn :: nat
            have "sram s \<in> ca_N cache_comp"
              by (smt mem_Collect_eq state.select_convs(1) state_N_init state_N_witness_def t0)
            then have "nn \<notin> {0..length (sram s) - 1} \<or> ca_set (SOME c. c \<in> sram s ! nn) = nn"
              by (metis (no_types) Suc_pred' atLeastAtMost_iff atLeastatMost_empty_iff2 ca_length ca_set_nonempty ca_set_num card_0_eq card_atLeastAtMost finite_atLeastAtMost neq0_conv some_in_eq zero_less_diff) 
          }
          then show "\<forall>n\<in>{0..length (sram s) - 1}. ca_set (SOME c. c \<in> sram s ! n) = n"
            by blast
        qed
      then have line_diff: "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                            (replace_policy ((sram s) ! l1)) \<noteq> (replace_policy ((sram s) ! l2))"
        proof -
          show ?thesis
            by (metis (no_types) caset_line)
        qed
      have policy_length: "card policy_line = card {0..length (sram s) - 1}"
        using length_finite length_nonempty line_diff a5
        by (simp add: policy_line_length)
      then have policy_length2: "card policy_line = length (sram s)"
        using cache_set_size t0 by auto
      then have out1: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)} =
                       {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        by auto
      have s1: "\<forall>e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e0: "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e0 caset_line a5 by auto
            then have "\<exists>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. d = e"
              using e0 by auto
            then have "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have s2: "\<forall>e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e1: "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e1 by auto
            moreover have "\<forall>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. fst (fst d) \<in> {0..length (sram s) - 1}"
              using caset_line a5 by auto
            ultimately have "\<exists>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. d = e"
              by (smt caset_line e1 a5 mem_Collect_eq)
            then have "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have out_equal: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))} =
                       {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using s1 s2 by blast
      then have out2: "execution (fst mr) s e = {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using out out1 by auto
      have finite_out: "finite {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        by auto
      have nonempty_out: "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} \<noteq> {}"
        by auto
      have value_out: "\<forall>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. snd d = 1/length (sram s)"
        by auto
      have "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} =
           1/length (sram s) * card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using cache_set_size2[where ?w = "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}" and
                                    ?P = "snd" and
                                    ?i = "1/length (sram s)"]
              finite_out nonempty_out value_out by blast
      moreover have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} = length (sram s)"
      proof -
        {
          have "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                ((l1, Miss), 1/length (sram s)) \<noteq> ((l2, Miss), 1/length (sram s))"
            by auto
          then have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1 / real (length (sram s)))} =
                     card {0..length (sram s) - 1}"
            using length_finite length_nonempty
            by (simp add: policy_line_length)
          then show ?thesis
            using cache_set_size t0 by auto
        }
      qed
      ultimately show ?thesis
        using of_nat_0 out2 by force 
    }
  qed

lemma read_sum_one_h4:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "policy_line = {t. \<exists>l \<in> {0..length (sram s) - 1}. t = replace_policy ((sram s) ! l)}"
      and a6: "owned r_line \<noteq> Some (thread (fst mr))"
    shows "folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  proof -
    {
      have exi_redir: "redir_set < length (sram s)"
        using state_N_init unfolding state_N_witness_def using mem_mapping
        by (smt a0 a1 map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
      have out: "execution (fst mr) s e = {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)}"
        unfolding execution_def rp_read_observe_def Let_def
        using t0 t1 a0 a1 a2 a3 a4 a5 a6 by auto
      have length_finite: "finite {0..length (sram s) - 1}"
        by blast
      have length_nonempty: "{0..length (sram s) - 1} \<noteq> {}"
        using atLeastatMost_empty_iff by blast
      have caset_line: "\<forall>l \<in> {0..length (sram s) - 1}. ca_set (replace_policy ((sram s) ! l)) = l"
        unfolding replace_policy_def
        proof -
          { 
            fix nn :: nat
            have "sram s \<in> ca_N cache_comp"
              by (smt mem_Collect_eq state.select_convs(1) state_N_init state_N_witness_def t0)
            then have "nn \<notin> {0..length (sram s) - 1} \<or> ca_set (SOME c. c \<in> sram s ! nn) = nn"
              by (metis (no_types) Suc_pred' atLeastAtMost_iff atLeastatMost_empty_iff2 ca_length ca_set_nonempty ca_set_num card_0_eq card_atLeastAtMost finite_atLeastAtMost neq0_conv some_in_eq zero_less_diff) 
          }
          then show "\<forall>n\<in>{0..length (sram s) - 1}. ca_set (SOME c. c \<in> sram s ! n) = n"
            by blast
        qed
      then have line_diff: "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                            (replace_policy ((sram s) ! l1)) \<noteq> (replace_policy ((sram s) ! l2))"
        proof -
          show ?thesis
            by (metis (no_types) caset_line)
        qed
      have policy_length: "card policy_line = card {0..length (sram s) - 1}"
        using length_finite length_nonempty line_diff a5
        by (simp add: policy_line_length)
      then have policy_length2: "card policy_line = length (sram s)"
        using cache_set_size t0 by auto
      then have out1: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/card policy_line)} =
                       {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        by auto
      have s1: "\<forall>e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e0: "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e0 caset_line a5 by auto
            then have "\<exists>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. d = e"
              using e0 by auto
            then have "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have s2: "\<forall>e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}.
                 e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
        proof -
          {
            fix e
            assume e1: "e \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
            have "fst (fst e) \<in> {0..length (sram s) - 1}"
              using e1 by auto
            moreover have "\<forall>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. fst (fst d) \<in> {0..length (sram s) - 1}"
              using caset_line a5 by auto
            ultimately have "\<exists>d \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}. d = e"
              by (smt caset_line e1 a5 mem_Collect_eq)
            then have "e \<in> {t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))}"
              by auto
          }
          then show ?thesis by blast
        qed
      have out_equal: "{t. \<exists>r'_line \<in> policy_line. t = ((ca_set r'_line, Miss), 1/length (sram s))} =
                       {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using s1 s2 by blast
      then have out2: "execution (fst mr) s e = {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using out out1 by auto
      have finite_out: "finite {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        by auto
      have nonempty_out: "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} \<noteq> {}"
        by auto
      have value_out: "\<forall>d \<in> {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}. snd d = 1/length (sram s)"
        by auto
      have "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} =
           1/length (sram s) * card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
        using cache_set_size2[where ?w = "{t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}" and
                                    ?P = "snd" and
                                    ?i = "1/length (sram s)"]
              finite_out nonempty_out value_out by blast
      moreover have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))} = length (sram s)"
      proof -
        {
          have "\<forall>l1 l2. l1 \<in> {0..length (sram s) - 1} \<and> l2 \<in> {0..length (sram s) - 1} \<and> l1 \<noteq> l2 \<longrightarrow>
                ((l1, Miss), 1/length (sram s)) \<noteq> ((l2, Miss), 1/length (sram s))"
            by auto
          then have "card {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1 / real (length (sram s)))} =
                     card {0..length (sram s) - 1}"
            using length_finite length_nonempty
            by (simp add: policy_line_length)
          then show ?thesis
            using cache_set_size t0 by auto
        }
      qed
      ultimately show ?thesis
        using of_nat_0 out2 by force 
    }
  qed

lemma read_sum_one:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
      proof -
        {
          fix mr
          assume t0: "mr \<in> mem_req mm_comp"
          have "\<forall>s \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
          proof -
            {
              fix s
              assume t1: "s \<in> state_N"
              have "folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
                using read_sum_one_h1 read_sum_one_h2 read_sum_one_h3 read_sum_one_h4 t0 t1
                by meson 
            }
            then show ?thesis by blast
          qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed

interpretation CM state_N state_E "mem_req mm_comp" execution
  apply standard
  using mem_finite mem_nonempty mem_unique mem_positive mem_sum_one
        read_finite read_nonempty read_unique read_positive read_sum_one
        stateN_finite stateN_nonempty stateE_nonempty stateE_subset
  by auto


subsection \<open>Proofs of Correctness\<close>

lemma one_changed1:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "owned r_line = Some (thread (fst mr))"
      and a6: "lock r_line = protect (fst mr)"
      and a7: "r_line' = replace_line r_line (fst mr)"
      and a8: "newset = insert r_line' (redir_ca - {r_line})"
    shows "card ((sram (the_elem (rp_read s (fst mr))))!redir_set \<inter> (sram s)!redir_set) =
           card ((sram s)!redir_set) - 1"
  proof -
    {
      have exi_redir: "redir_set < length (sram s)"
        using state_N_init unfolding state_N_witness_def using mem_mapping
        by (smt a0 a1 map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
      have t2: "sram s \<in> ca_N cache_comp"
        using state_N_init t0 unfolding state_N_witness_def
        proof -
          assume "state_N = {t. \<exists>c\<in>ca_N cache_comp. t = \<lparr>sram = c, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
          then have "state_N = {s. \<exists>Cs. Cs \<in> ca_N cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
            by meson
          then have "\<exists>Cs. Cs \<in> ca_N cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>"
            using t0 by blast
          then show ?thesis
            by force
        qed
      have probe_fails: "\<nexists>b. b \<in> redir_ca \<and> ca_tag b = tag (fst mr) \<and> valid b \<and> owned b = Some (thread (fst mr))"
        using a3 unfolding probe_line_def by force
      have t3: "r_line \<in> redir_ca"
        using a2 exi_redir a4 unfolding replace_policy_def
        by (simp add: ca_set_nonempty some_in_eq t2) 
      then have tag_diff: "\<not> (ca_tag r_line = tag (fst mr) \<and> valid r_line \<and> owned r_line = Some (thread (fst mr)))"
        using probe_fails by auto
      have tag_same: "ca_tag r_line' = tag (fst mr) \<and> valid r_line' \<and> owned r_line' = Some (thread (fst mr))"
        using a7 unfolding replace_line_def by simp
      have t4: "r_line' \<notin> redir_ca"
        using probe_fails tag_same by blast
      then have "newset \<inter> redir_ca = redir_ca - {r_line}"
        using a8 by blast
      then have re: "card (newset \<inter> redir_ca) = card redir_ca - 1"
        by (simp add: card_Diff_subset_Int t3)
      have "rp_read s (fst mr) = {s\<lparr>sram := list_update (sram s) redir_set newset\<rparr>}"
        unfolding rp_read_def Let_def
        using a0 a1 a2 a3 a4 a5 a6 a7 a8 mem_occupy t1 by auto
      then have "the_elem (rp_read s (fst mr)) = s\<lparr>sram := list_update (sram s) redir_set newset\<rparr>"
        unfolding the_elem_def by auto
      then have "(sram (the_elem (rp_read s (fst mr))))!redir_set = newset"
        using exi_redir by simp
      then show ?thesis
        using re a2 by blast 
    }
  qed

lemma remain_same1:
  assumes t0: "s \<in> state_N"
      and t1: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "owned r_line = Some (thread (fst mr))"
      and a6: "lock r_line = protect (fst mr)"
      and a7: "newset = insert (replace_line r_line (fst mr)) (redir_ca - {r_line})"
    shows "\<forall>l \<noteq> redir_set. (sram s)!l = (sram (the_elem (rp_read s (fst mr))))!l"
  proof -
    {
      fix l assume tl: "l \<noteq> redir_set"
      have "(sram s)!l = (sram (the_elem (rp_read s (fst mr))))!l"
      proof -
        {
          have "rp_read s (fst mr) = {s\<lparr>sram := list_update (sram s) redir_set newset\<rparr>}"
            unfolding rp_read_def Let_def
            using a0 a1 a2 a3 a4 a5 a6 a7 mem_occupy t1 by auto 
          then show ?thesis using tl by auto
        }
      qed
    }
    then show ?thesis by blast
  qed

lemma one_changed_remain_same2:
  assumes t0: "s0 \<in> state_N"
      and t1: "\<forall>l < length (sram s0). \<forall>e \<in> (sram s0)!l. valid e"
      and t2: "mr \<in> mem_req mm_comp"
      and a0: "maps = map_H s0"
      and a1: "redir_set = the (maps (index (fst mr)))"
      and a2: "redir_ca = (sram s0) ! redir_set"
      and a3: "\<not> (probe_line redir_ca (fst mr))"
      and a4: "r_line = replace_policy redir_ca"
      and a5: "policy_line = {t. \<exists>l \<in> {0..length (sram s0) - 1}. t = replace_policy ((sram s0) ! l)}"
      and a6: "owned r_line = Some (thread (fst mr))"
      and a7: "lock r_line \<noteq> protect (fst mr)"
    shows "\<forall>s' \<in> rp_read s0 (fst mr). \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
  proof -
    {
      fix s' assume ts: "s' \<in> rp_read s0 (fst mr)"
      have "\<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
      proof -
        {
          have iowned: "thread (fst mr) = H"
            by (simp add: mem_occupy t2)
          have exi_redir: "redir_set < length (sram s0)"
            using state_N_init unfolding state_N_witness_def using mem_mapping
            by (smt a0 a1 map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t2)
          have t3: "sram s0 \<in> ca_N cache_comp"
            using state_N_init t0 unfolding state_N_witness_def
            proof -
              assume "state_N = {t. \<exists>c\<in>ca_N cache_comp. t = \<lparr>sram = c, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
              then have "state_N = {s. \<exists>Cs. Cs \<in> ca_N cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
                by meson
              then have "\<exists>Cs. Cs \<in> ca_N cache_comp \<and> s0 = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>"
                using t0 by blast
              then show ?thesis
                by force
            qed
          have probe_fails: "\<nexists>b. b \<in> redir_ca \<and> ca_tag b = tag (fst mr) \<and> valid b \<and> owned b = Some (thread (fst mr))"
            using a3 unfolding probe_line_def by force
          have t4: "r_line \<in> redir_ca"
            using a2 exi_redir a4 unfolding replace_policy_def
            by (simp add: ca_set_nonempty some_in_eq t3) 
          then have tag_diff: "\<not> (ca_tag r_line = tag (fst mr) \<and> valid r_line \<and> owned r_line = Some (thread (fst mr)))"
            using probe_fails by auto
          have out: "rp_read s0 (fst mr) = {t. \<exists>r'_line \<in> policy_line. let newset = insert (drop_line r'_line) (((sram s0) ! (ca_set r'_line)) - {r'_line}) in
                                               t = s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) newset\<rparr>}"
            unfolding rp_read_def Let_def
            using a0 a1 a2 a3 a4 a5 a6 a7 iowned by auto
          then have "\<exists>r'_line \<in> policy_line.
                      s' = (let newset = insert (drop_line r'_line) (((sram s0) ! (ca_set r'_line)) - {r'_line}) in
                            s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) newset\<rparr>)"
            using ts by auto
          then obtain r'_line where t5: "r'_line \<in> policy_line \<and>
                                         s' = (let newset = insert (drop_line r'_line) (((sram s0) ! (ca_set r'_line)) - {r'_line}) in
                                               s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) newset\<rparr>)"
            by auto
          have r'_length: "ca_set r'_line < length (sram s0)"
            using t5 by (smt Suc_pred' a5 atLeastAtMost_iff ca_length ca_set_nonempty ca_set_num less_Suc_eq_le mem_Collect_eq replace_policy_def some_in_eq t3)
          have r'_belong: "r'_line \<in> (sram s0) ! (ca_set r'_line)"
            using t5 by (smt Suc_pred' a5 atLeastAtMost_iff ca_length ca_set_nonempty ca_set_num less_Suc_eq_le mem_Collect_eq replace_policy_def some_in_eq t3)
          have tag_valid: "valid r'_line"
            using t1 r'_belong r'_length by blast
          let ?r'_line' = "drop_line r'_line"
          have tag_drop: "valid ?r'_line' = False \<and> lock ?r'_line' = False \<and> owned ?r'_line' = None"
            unfolding drop_line_def by simp
          have t6: "?r'_line' \<notin> (sram s0) ! (ca_set r'_line)"
            using r'_length t1 tag_drop by blast
          let ?newset = "insert ?r'_line' (((sram s0) ! (ca_set r'_line)) - {r'_line})"
          have "?newset \<inter> ((sram s0) ! (ca_set r'_line)) = ((sram s0) ! (ca_set r'_line)) - {r'_line}"
            using t6 by auto
          then have re: "card (?newset \<inter> ((sram s0) ! (ca_set r'_line))) = card ((sram s0) ! (ca_set r'_line)) - 1"
            by (simp add: card_Diff_subset_Int r'_belong)
          have out1: "s' = s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) ?newset\<rparr>"
            using t5 by simp
          then have "sram s' = list_update (sram s0) (ca_set r'_line) ?newset"
            by auto
          then have "\<exists>!l. l = ca_set r'_line \<and> (\<forall>l' \<noteq> l. sram s0 ! l' = sram s' ! l') \<and>
                          card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1"
            using re nth_list_update_eq r'_length by auto 
          then show ?thesis
            by (metis \<open>sram s' = (sram s0) [ca_set r'_line := insert (drop_line r'_line) (sram s0 ! ca_set r'_line - {r'_line})]\<close> insertI1 nth_list_update_eq r'_length t6) 
        }
      qed
    }
    then show ?thesis by auto
  qed

lemma one_changed_remain_same3:
  "\<forall>i \<in> mem_req mm_comp. \<forall>s0 \<in> state_E. \<forall>s' \<in> rp_read s0 (fst i).
    \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
  proof -
    {
      fix i assume t0: "i \<in> mem_req mm_comp"
      have "\<forall>s0 \<in> state_E. \<forall>s' \<in> rp_read s0 (fst i).
              \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
      proof -
        {
          fix s0 assume t1: "s0 \<in> state_E"
          have "\<forall>s' \<in> rp_read s0 (fst i).
                  \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
          proof -
            {
              fix s' assume t2: "s' \<in> rp_read s0 (fst i)"
              have "\<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
              proof -
                {
                  have iowned: "thread (fst i) = H"
                    by (simp add: mem_occupy t0)
                  then have "(if thread (fst i) = H then map_H s0 else map_L s0) = map_H s0"
                    by auto
                  let ?maps = "map_H s0"
                  let ?redir_set = "the (?maps (index (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_E_init unfolding state_E_witness_def using mem_mapping
                    by (smt caE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t1)
                  let ?redir_ca = "(sram s0) ! ?redir_set"
                  have t3: "sram s0 \<in> ca_E cache_comp"
                    using state_E_init unfolding state_E_witness_def
                    proof -
                      assume "state_E = {t. \<exists>c\<in>ca_E cache_comp. t = \<lparr>sram = c, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
                      then have "state_E = {s. \<exists>Cs. Cs \<in> ca_E cache_comp \<and> s = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>}"
                        by meson
                      then have "\<exists>Cs. Cs \<in> ca_E cache_comp \<and> s0 = \<lparr>sram = Cs, map_H = map_conf mm_comp, map_L = map_conf mm_comp\<rparr>"
                        using t1 by blast
                      then show ?thesis
                        by fastforce
                    qed
                  then have setowned: "\<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). owned e = Some L"
                    using caE_occupy by blast
                  then have "\<nexists>b. b \<in> ?redir_ca \<and> ca_tag b = tag (fst i) \<and> valid b \<and> owned b = Some (thread (fst i))"
                    using iowned exi_redir by auto
                  then have c1: "\<not> probe_line ?redir_ca (fst i)"
                    unfolding probe_line_def by blast
                  let ?r_line = "replace_policy ?redir_ca"
                  have "?r_line \<in> ?redir_ca"
                    unfolding replace_policy_def
                    using caE_init ca_set_nonempty some_in_eq t3 exi_redir by blast
                  then have "owned ?r_line = Some L"
                    using setowned exi_redir by blast
                  then have c2: "owned ?r_line \<noteq> Some (thread (fst i))"
                    using iowned by auto
                  let ?policy_line = "{t. \<exists>l \<in> {0..length (sram s0) - 1}. t = replace_policy ((sram s0) ! l)}"
                  have out: "rp_read s0 (fst i) = {t. \<exists>r'_line \<in> ?policy_line.
                                                      if ca_set r'_line = ?redir_set then
                                                        let newset = insert (replace_line r'_line (fst i)) (fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i)) in
                                                            t = s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) newset,
                                                                   map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>
                                                      else let newset = insert (replace_line r'_line (fst i)) (fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i));
                                                               new_redir_ca = fix_line ?redir_ca (fst i) in
                                                        t = s0\<lparr>sram := list_update (list_update (sram s0) (ca_set r'_line) newset) ?redir_set new_redir_ca,
                                                               map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>}"
                    unfolding rp_read_def Let_def
                    using c1 c2 by (simp add: iowned)
                  then have "\<exists>r'_line \<in> ?policy_line.
                              s' = (if ca_set r'_line = ?redir_set then
                                      let newset = insert (replace_line r'_line (fst i)) (fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i)) in
                                          s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) newset,
                                             map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>
                                    else let newset = insert (replace_line r'_line (fst i)) (fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i));
                                             new_redir_ca = fix_line ?redir_ca (fst i) in
                                      s0\<lparr>sram := list_update (list_update (sram s0) (ca_set r'_line) newset) ?redir_set new_redir_ca,
                                         map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>)"
                    using t2 by auto 
                  then obtain r'_line where t4: "r'_line \<in> ?policy_line \<and>
                                                 s' = (if ca_set r'_line = ?redir_set then
                                                         let newset = insert (replace_line r'_line (fst i)) (fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i)) in
                                                             s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) newset,
                                                                map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>
                                                       else let newset = insert (replace_line r'_line (fst i)) (fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i));
                                                                new_redir_ca = fix_line ?redir_ca (fst i) in
                                                         s0\<lparr>sram := list_update (list_update (sram s0) (ca_set r'_line) newset) ?redir_set new_redir_ca,
                                                            map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>)"
                    by auto
                  have r'_length: "ca_set r'_line < length (sram s0)"
                    using t4
                    proof -
                      obtain nn :: "cache_line \<Rightarrow> nat" where
                        "(r'_line \<notin> {c. \<exists>n. n \<in> {0..length (sram s0) - 1} \<and> c = replace_policy (sram s0 ! n)} \<or> nn r'_line \<in> {0..length (sram s0) - 1} \<and> r'_line = (SOME c. c \<in> sram s0 ! nn r'_line)) \<and> (r'_line \<in> {c. \<exists>n. n \<in> {0..length (sram s0) - 1} \<and> c = replace_policy (sram s0 ! n)} \<or> (\<forall>n. n \<notin> {0..length (sram s0) - 1} \<or> r'_line \<noteq> (SOME c. c \<in> sram s0 ! n)))"
                        using replace_policy_def by moura
                      then have f1: "nn r'_line \<in> {0..length (sram s0) - 1} \<and> r'_line = (SOME c. c \<in> sram s0 ! nn r'_line)"
                        using t4 by blast
                      then have f2: "nn r'_line \<in> Collect ((\<le>) 0) \<and> length (sram s0) - 1 \<in> Collect ((\<le>) (nn r'_line))"
                        using atLeastAtMost_iff by blast
                      have f3: "sram s0 \<in> ca_N cache_comp"
                        using caE_init t3 by blast
                      then have f4: "length (sram s0) = Suc (length (sram s0) - 1)"
                        by (meson Suc_pred' ca_length)
                      have "\<forall>n na. (Suc na \<in> Collect ((<) n)) = (na \<in> Collect ((\<le>) n))"
                        by (simp add: less_Suc_eq_le)
                      then show ?thesis
                        using f4 f3 f2 f1 by (metis ca_set_nonempty ca_set_num mem_Collect_eq some_in_eq)
                    qed
                  have r'_belong: "r'_line \<in> (sram s0) ! (ca_set r'_line)"
                    using t4
                    proof -
                      have f1: "sram s0 \<in> ca_N cache_comp"
                        using caE_init t3 by blast
                      obtain nn :: "cache_line \<Rightarrow> nat" where
                        "(r'_line \<notin> {c. \<exists>n. n \<in> {0..length (sram s0) - 1} \<and> c = replace_policy (sram s0 ! n)} \<or> nn r'_line \<in> {0..length (sram s0) - 1} \<and> r'_line = (SOME c. c \<in> sram s0 ! nn r'_line)) \<and> (r'_line \<in> {c. \<exists>n. n \<in> {0..length (sram s0) - 1} \<and> c = replace_policy (sram s0 ! n)} \<or> (\<forall>n. n \<notin> {0..length (sram s0) - 1} \<or> r'_line \<noteq> (SOME c. c \<in> sram s0 ! n)))"
                        using replace_policy_def by moura
                      then have f2: "nn r'_line \<in> {0..length (sram s0) - 1} \<and> r'_line = (SOME c. c \<in> sram s0 ! nn r'_line)"
                        using t4 by blast
                      then have f3: "length (sram s0) \<in> Collect ((<) (nn r'_line))"
                        using f1 by (metis Suc_pred' atLeastAtMost_iff ca_length less_Suc_eq_le mem_Collect_eq)
                      then have f4: "(SOME c. c \<in> sram s0 ! nn r'_line) \<in> sram s0 ! nn r'_line"
                        using f1 by (simp add: ca_set_nonempty some_in_eq)
                      then have "nn r'_line = ca_set r'_line"
                        using f3 f2 f1 by (simp add: ca_set_num)
                      then show ?thesis
                      using f4 f2 by auto
                    qed
                  then have tag_diff: "the (owned r'_line) \<noteq> thread (fst i)"
                    using setowned r'_length iowned by auto 
                  {
                    assume r0: "ca_set r'_line = ?redir_set"
                    have fix_l: "fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i) = ((sram s0) ! (ca_set r'_line)) - {r'_line}"
                      unfolding fix_line_def using r'_length setowned iowned by auto
                    let ?r'_line' = "replace_line r'_line (fst i)"
                    have tag_same: "ca_tag ?r'_line' = tag (fst i) \<and> valid ?r'_line' \<and> owned ?r'_line' = Some (thread (fst i))"
                      unfolding replace_line_def by simp
                    have t5: "?r'_line' \<notin> (sram s0) ! (ca_set r'_line)"
                      using c1 probe_line_def r0 tag_same by auto
                    let ?newset = "insert ?r'_line' (((sram s0) ! (ca_set r'_line)) - {r'_line})"
                    have "?newset \<inter> ((sram s0) ! (ca_set r'_line)) = ((sram s0) ! (ca_set r'_line)) - {r'_line}"
                      using t5 by auto
                    then have re: "card (?newset \<inter> ((sram s0) ! (ca_set r'_line))) = card ((sram s0) ! (ca_set r'_line)) - 1"
                      by (simp add: card_Diff_subset_Int r'_belong)
                    have out1: "s' = s0\<lparr>sram := list_update (sram s0) (ca_set r'_line) ?newset,
                                        map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>"
                      using t4 fix_l r0 by auto
                    then have "sram s' = list_update (sram s0) (ca_set r'_line) ?newset"
                      by auto
                    then have "\<exists>!l. l = ca_set r'_line \<and> (\<forall>l' \<noteq> l. sram s0 ! l' = sram s' ! l') \<and>
                                    card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1"
                      using re nth_list_update_eq r'_length by auto 
                    then have ?thesis
                      by (metis \<open>sram s' = (sram s0) [ca_set r'_line := insert (replace_line r'_line (fst i)) (sram s0 ! ca_set r'_line - {r'_line})]\<close> insertI1 nth_list_update_eq r'_length t5) 
                  }
                  moreover
                  {
                    assume r1: "ca_set r'_line \<noteq> ?redir_set"
                    have fix_l: "fix_line (((sram s0) ! (ca_set r'_line)) - {r'_line}) (fst i) = ((sram s0) ! (ca_set r'_line)) - {r'_line}"
                      unfolding fix_line_def using r'_length setowned iowned by auto
                    let ?r'_line' = "replace_line r'_line (fst i)"
                    have tag_same: "ca_tag ?r'_line' = tag (fst i) \<and> valid ?r'_line' \<and> owned ?r'_line' = Some (thread (fst i))"
                      unfolding replace_line_def by simp
                    have t5: "?r'_line' \<notin> (sram s0) ! (ca_set r'_line)"
                      using \<open>owned (replace_policy (sram s0 ! the (map_H s0 (index (fst i))))) = Some L\<close> c2 r'_length setowned tag_same by force
                    let ?newset = "insert ?r'_line' (((sram s0) ! (ca_set r'_line)) - {r'_line})"
  
                    have "?newset \<inter> ((sram s0) ! (ca_set r'_line)) = ((sram s0) ! (ca_set r'_line)) - {r'_line}"
                      using t5 by auto
                    then have re: "card (?newset \<inter> ((sram s0) ! (ca_set r'_line))) = card ((sram s0) ! (ca_set r'_line)) - 1"
                      by (simp add: card_Diff_subset_Int r'_belong)
  
                    have fix_ll: "fix_line ?redir_ca (fst i) = ?redir_ca"
                      unfolding fix_line_def using setowned iowned exi_redir by auto
                    let ?new_redir_ca = "?redir_ca"
                    have out2: "s' = s0\<lparr>sram := list_update (list_update (sram s0) (ca_set r'_line) ?newset) ?redir_set ?new_redir_ca,
                                        map_H := swap_map (map_H s0) ?redir_set (ca_set r'_line)\<rparr>"
                      using t4
                      by (simp add: \<open>fix_line (sram s0 ! the (map_H s0 (index (fst i)))) (fst i) = sram s0 ! the (map_H s0 (index (fst i)))\<close> fix_l r1) 
                    have "list_update (list_update (sram s0) (ca_set r'_line) ?newset) ?redir_set ?new_redir_ca = list_update (sram s0) (ca_set r'_line) ?newset"
                      using fix_ll by (simp add: list_update_swap r1)
                    then have "sram s' = list_update (sram s0) (ca_set r'_line) ?newset"
                      using out2 by auto
                    then have "\<exists>!l. l = ca_set r'_line \<and> (\<forall>l' \<noteq> l. sram s0 ! l' = sram s' ! l') \<and>
                                    card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1"
                      using re nth_list_update_eq r'_length by auto 
                    have ?thesis
                      by (metis \<open>\<exists>!l. l = ca_set r'_line \<and> (\<forall>l'. l' \<noteq> l \<longrightarrow> sram s0 ! l' = sram s' ! l') \<and> card (sram s' ! l \<inter> sram s0 ! l) = card (sram s0 ! l) - 1\<close> \<open>sram s' = (sram s0) [ca_set r'_line := insert (replace_line r'_line (fst i)) (sram s0 ! ca_set r'_line - {r'_line})]\<close> insertI1 nth_list_update_eq r'_length t5)
                  }
                  ultimately have ?thesis
                    by linarith 
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


subsection \<open>Proofs of Security Model\<close>

lemma read_not_zero:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
      proof -
        {
          fix mr
          assume t0: "mr \<in> mem_req mm_comp"
          have "\<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
          proof -
            {
              fix s
              assume t1: "s \<in> state_E"
              have "\<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
              proof -
                {
                  have "execution (fst mr) s e = {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
                    unfolding execution_def using mem_cache_miss t0 t1 by auto
                  moreover have "length (sram s) \<noteq> 0"
                    using cache_set_size stateE_subset t1 by fastforce
                  ultimately show ?thesis
                    by simp 
                }
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

lemma read_uniform:
  "\<forall>e. \<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
    snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req mm_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
             snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
      proof -
        {
          fix mr assume t0: "mr \<in> mem_req mm_comp"
          have "\<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
                 snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
          proof -
            {
              fix s assume t1: "s \<in> state_E"
              have "\<forall>d \<in> execution (fst mr) s e.
                     snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
              proof -
                {
                  fix d assume "d \<in> execution (fst mr) s e"
                  have emr: "execution (fst mr) s e = {t. \<exists>r \<in> {0..length (sram s) - 1}. t = ((r, Miss), 1/length (sram s))}"
                    unfolding execution_def using mem_cache_miss
                    using t0 t1 by blast
                  have pmf_m: "\<forall>m \<in> mem_req mm_comp. \<exists>!t \<in> execution (fst m) s e. t = (fst d, snd d)"
                    using \<open>d \<in> execution (fst mr) s e\<close> execution_def mem_cache_miss t0 t1 by auto
                  then have makedist_m: "\<forall>m \<in> mem_req mm_comp. ((fst m, fst d), snd m * snd d) \<in> makeDist s e"
                    unfolding makeDist_def using emr by fastforce
                  then have set_equal: "{u. u \<in> makeDist s e \<and> snd (fst u) = fst d} =
                                        {t. \<exists>m \<in> mem_req mm_comp. t = ((fst m, fst d), snd m * snd d)}"
                    by (smt Collect_cong Pair_inject execution_def makeDist_def mem_Collect_eq mem_cache_miss pmf_m surjective_pairing t1)
                  have sum1: "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>m \<in> mem_req mm_comp. t = ((fst m, fst d), snd m * snd d)} =
                              folds (\<lambda>t p. snd t * snd d + p) 0 (mem_req mm_comp)" 
                    using folds_plus_times_input2[where ?w = "mem_req mm_comp" and ?d = "d"]
                          mem_finite mem_nonempty mem_unique inputdist_nonempty by auto 
                  have sum2: "folds (\<lambda>t p. snd t * snd d + p) 0 (mem_req mm_comp) = snd d * (folds (\<lambda>t p. snd t + p) 0 (mem_req mm_comp))"
                    using folds_plus_times_input[where ?w = "mem_req mm_comp" and ?i = "snd d"]
                          mem_finite mem_nonempty mem_unique inputdist_nonempty by auto
                  have "snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
                    using set_equal sum1 sum2 mem_sum_one by simp
                }
                then show ?thesis by auto
              qed
            }
            then show ?thesis by auto
          qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed

end
