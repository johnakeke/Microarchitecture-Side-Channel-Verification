section \<open>Set Associative Cache\<close>

theory CM_SaSpec
  imports Main CM_SecurityModel
begin

subsection \<open>Data type, Basic components\<close>

(*Basic data structures*)
type_synonym tagmask = nat
type_synonym setbits = nat
type_synonym setindex = nat
type_synonym wayindex = nat

datatype cachehit = Hit | Miss

datatype event = SA_READ

(*Memory blocks*)
record memory_request =
  tag :: tagmask
  index :: setbits

(*Cache structure*)
record cache_line =
  ca_tag :: tagmask
  ca_set :: setindex
  ca_way :: wayindex
  valid :: bool

type_synonym cache = "(cache_line set) list"

type_synonym mapping = "setbits \<rightharpoonup> setindex"

(*State Machine*)
record state =
  sram :: cache
  maps :: mapping

subsection \<open>Set Associative cache model specifications\<close>

definition replace_policy :: "cache_line set \<Rightarrow> cache_line"
  where "replace_policy cs \<equiv> SOME l. l \<in> cs"

definition probe_line :: "cache_line set \<Rightarrow> memory_request \<Rightarrow> bool"
  where "probe_line cs mr \<equiv> \<exists>b. b \<in> cs \<and> ca_tag b = tag mr \<and> valid b"

definition replace_line :: "cache_line \<Rightarrow> memory_request \<Rightarrow> cache_line"
  where "replace_line cl mr \<equiv> cl\<lparr>ca_tag := tag mr, valid := True\<rparr>"

definition sa_read :: "state \<Rightarrow> memory_request \<Rightarrow> state set" where
  "sa_read s mr \<equiv>
      let redir_set = the ((maps s) (index mr));
          redir_ca = (sram s) ! redir_set in
      if probe_line redir_ca mr then {s}
      else let r_line = replace_policy redir_ca;
               newset = insert (replace_line r_line mr) (redir_ca - {r_line}) in
           {s\<lparr>sram := list_update (sram s) redir_set newset\<rparr>}"


subsection \<open>Instantiation\<close>

record cache_NE =
  ca_N :: "cache set"
  ca_E :: "cache set"
  map_conf :: "mapping"
  mem_req :: "(memory_request \<times> real) set"

consts cache_comp :: cache_NE

definition cache_comp_witness :: "cache_NE"
  where "cache_comp_witness \<equiv> \<lparr>ca_N = {[{(\<lparr>ca_tag = 1, ca_set = 0, ca_way = 0, valid = True\<rparr>)}]},
                               ca_E = {[{(\<lparr>ca_tag = 1, ca_set = 0, ca_way = 0, valid = True\<rparr>)}]},
                               map_conf = (\<lambda>t. if t = 0 then Some 0 else None),
                               mem_req = {(\<lparr>tag = 0, index = 0\<rparr>, 1)}\<rparr>"

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
  
  map_range: "\<forall>c \<in> (ca_N cache_comp). (\<forall>i. (map_conf cache_comp) i \<noteq> None \<longrightarrow> the ((map_conf cache_comp) i) < length c)"
  map_diff: "\<forall>i j. i \<noteq> j \<and> (map_conf cache_comp) i \<noteq> None \<and> (map_conf cache_comp) j \<noteq> None \<longrightarrow> the ((map_conf cache_comp) i) \<noteq> the ((map_conf cache_comp) j)"
  
  mem_finite: "finite (mem_req cache_comp)"
  mem_nonempty: "card (mem_req cache_comp) > 0"
  mem_unique: "\<forall>i j. i \<in> (mem_req cache_comp) \<and> j \<in> (mem_req cache_comp) \<and> i \<noteq> j \<longrightarrow> index (fst i) \<noteq> index (fst j)"
  mem_positive: "\<forall>i \<in> (mem_req cache_comp). snd i > 0"
  mem_sum_one: "folds (\<lambda>t p. snd t + p) 0 (mem_req cache_comp) = 1"
  mem_occupy: "\<forall>i \<in> (mem_req cache_comp). \<forall>c \<in> (ca_E cache_comp). \<forall>l < length c. \<forall>e \<in> (c!l). tag (fst i) \<noteq> ca_tag e"
  mem_mapping: "\<forall>i \<in> (mem_req cache_comp). (map_conf cache_comp) (index (fst i)) \<noteq> None"
  
  apply(intro exI[of _ cache_comp_witness])
  unfolding cache_comp_witness_def by auto

(*state N*)
consts state_N :: "state set"

definition state_N_witness :: "state set"
  where "state_N_witness \<equiv> {t. \<exists>c \<in> (ca_N cache_comp). t = \<lparr>sram = c, maps = (map_conf cache_comp)\<rparr>}"

specification (state_N)
  state_N_init: "state_N = state_N_witness"
  by simp

lemma stateN_finite: "finite state_N"
  proof -
    {
      have "\<forall>c \<in> (ca_N cache_comp). finite {t. \<exists>c \<in> (ca_N cache_comp). t = \<lparr>sram = c, maps = (map_conf cache_comp)\<rparr>}"
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
  where "state_E_witness \<equiv> {t. \<exists>c \<in> (ca_E cache_comp). t = \<lparr>sram = c, maps = (map_conf cache_comp)\<rparr>}"

specification (state_E)
  state_E_init: "state_E = state_E_witness"
  by simp

lemma stateE_nonempty: "state_E \<noteq> {}"
  using state_E_init state_E_witness_def caE_nonempty
  by blast

lemma stateE_subset: "state_E \<subseteq> state_N"
  using state_N_init state_N_witness_def state_E_init state_E_witness_def
  by (smt Collect_mono_iff caE_init subset_eq)

(*Observation*)
definition sa_read_observe :: "state \<Rightarrow> memory_request \<Rightarrow> ((setindex \<times> cachehit) \<times> real) set" where
  "sa_read_observe s mr \<equiv>
      let redir_set = the ((maps s) (index mr));
          redir_ca = (sram s) ! redir_set in
      if probe_line redir_ca mr then {((redir_set, Hit), 1)}
      else {((redir_set, Miss), 1)}"

lemma mem_cache_miss:
  "\<forall>i \<in> mem_req cache_comp. \<forall>s0 \<in> state_E. sa_read_observe s0 (fst i) = {((the ((maps s0) (index (fst i))), Miss), 1)}"
  proof -
    {
      fix i
      assume t0: "i \<in> mem_req cache_comp"
      have "\<forall>s0 \<in> state_E. sa_read_observe s0 (fst i) = {((the (maps s0 (index (fst i))), Miss), 1)}"
      proof -
        {
          fix s0
          assume t1: "s0 \<in> state_E"
          have "sa_read_observe s0 (fst i) = {((the (maps s0 (index (fst i))), Miss), 1)}"
          proof -
            {
              let ?redir_set = "the ((maps s0) (index (fst i)))"
              have exi_redir: "?redir_set < length (sram s0)"
                using state_E_init unfolding state_E_witness_def using mem_mapping
                by (smt caE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t1)
              let ?redir_ca = "(sram s0) ! ?redir_set"
              have "sram s0 \<in> ca_E cache_comp"
                using state_E_init unfolding state_E_witness_def
                proof -
                  assume "state_E = {t. \<exists>c\<in>ca_E cache_comp. t = \<lparr>sram = c, maps = map_conf cache_comp\<rparr>}"
                  then have "state_E = {s. \<exists>Cs. Cs \<in> ca_E cache_comp \<and> s = \<lparr>sram = Cs, maps = map_conf cache_comp\<rparr>}"
                    by (simp add: Bex_def_raw)
                  then have "\<exists>Cs. Cs \<in> ca_E cache_comp \<and> s0 = \<lparr>sram = Cs, maps = map_conf cache_comp\<rparr>"
                    using t1 by blast
                  then show ?thesis
                    by force
                qed
              then have setowned: "\<forall>i \<in> (mem_req cache_comp). \<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). tag (fst i) \<noteq> ca_tag e"
                using mem_occupy by auto
              then have "\<nexists>b. b \<in> ?redir_ca \<and> ca_tag b = tag (fst i) \<and> valid b"
                using exi_redir t0 by force
              then have c: "\<not> probe_line ?redir_ca (fst i)"
                unfolding probe_line_def by blast
              then have "sa_read_observe s0 (fst i) = {((?redir_set, Miss), 1)}"
                unfolding sa_read_observe_def Let_def by auto
            }
            then show ?thesis by blast
          qed
        }
        then show ?thesis by blast 
      qed
    }
    then show ?thesis by blast
  qed

(*pmf instantiate*)
definition execution :: "memory_request \<Rightarrow> state \<Rightarrow> event \<Rightarrow> ((setindex \<times> cachehit) \<times> real) set"
  where "execution mr s e \<equiv> sa_read_observe s mr"

lemma read_finite:
  "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_N. finite (execution (fst mr) s e)"
  unfolding execution_def sa_read_observe_def Let_def
  by simp

lemma read_nonempty:
  "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_N. execution (fst mr) s e \<noteq> {}"
  unfolding execution_def sa_read_observe_def Let_def
  by auto

lemma read_unique:
  "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_N. \<forall>m n. m \<in> (execution (fst mr) s e) \<and> n \<in> (execution (fst mr) s e) \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n"
  unfolding execution_def sa_read_observe_def Let_def
  by auto

lemma read_positive:
  "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_N. \<forall>d \<in> (execution (fst mr) s e). snd d \<ge> 0"
  unfolding execution_def sa_read_observe_def Let_def
  by auto

lemma read_sum_one:
  "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  using read_positive
  proof -
    {
      fix mm :: memory_request and ss :: state and ee :: event
      have "folds (\<lambda>t p. snd t + p) 0 (execution mm ss ee) = 1"
        unfolding execution_def sa_read_observe_def Let_def by simp
    }
    then show ?thesis by blast
  qed 

interpretation CM state_N state_E "mem_req cache_comp" execution
  apply standard
  using mem_finite mem_nonempty mem_unique mem_positive mem_sum_one
        read_finite read_nonempty read_unique read_positive read_sum_one
        stateN_finite stateN_nonempty stateE_nonempty stateE_subset
  by auto


subsection \<open>Proofs of Correctness\<close>

lemma one_changed:
  "\<forall>i \<in> mem_req cache_comp. \<forall>s0 \<in> state_E.
    card ((sram (the_elem (sa_read s0 (fst i))))!(the ((maps s0) (index (fst i)))) \<inter> (sram s0)!(the ((maps s0) (index (fst i))))) =
    card ((sram s0)!(the ((maps s0) (index (fst i))))) - 1"
  proof -
    {
      fix i assume t0: "i \<in> mem_req cache_comp"
      have "\<forall>s0 \<in> state_E. card ((sram (the_elem (sa_read s0 (fst i))))!(the ((maps s0) (index (fst i)))) \<inter> (sram s0)!(the ((maps s0) (index (fst i))))) =
                           card ((sram s0)!(the ((maps s0) (index (fst i))))) - 1"
      proof -
        {
          fix s0 assume t1: "s0 \<in> state_E"
          have "card ((sram (the_elem (sa_read s0 (fst i))))!(the ((maps s0) (index (fst i)))) \<inter> (sram s0)!(the ((maps s0) (index (fst i))))) =
                card ((sram s0)!(the ((maps s0) (index (fst i))))) - 1"
          proof -
            {
              let ?redir_set = "the ((maps s0) (index (fst i)))"
              have exi_redir: "?redir_set < length (sram s0)"
                using state_E_init unfolding state_E_witness_def using mem_mapping
                by (smt caE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t1)
              let ?redir_ca = "(sram s0) ! ?redir_set"
              have t2: "sram s0 \<in> ca_E cache_comp"
                using state_E_init unfolding state_E_witness_def
                proof -
                  assume "state_E = {t. \<exists>c\<in>ca_E cache_comp. t = \<lparr>sram = c, maps = map_conf cache_comp\<rparr>}"
                  then have "state_E = {s. \<exists>Cs. Cs \<in> ca_E cache_comp \<and> s = \<lparr>sram = Cs, maps = map_conf cache_comp\<rparr>}"
                    by (simp add: Bex_def_raw)
                  then have "\<exists>Cs. Cs \<in> ca_E cache_comp \<and> s0 = \<lparr>sram = Cs, maps = map_conf cache_comp\<rparr>"
                    using t1 by blast
                  then show ?thesis
                    by force
                qed
              then have setowned: "\<forall>i \<in> (mem_req cache_comp). \<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). tag (fst i) \<noteq> ca_tag e"
                using mem_occupy by auto
              then have probe_fails: "\<nexists>b. b \<in> ?redir_ca \<and> ca_tag b = tag (fst i) \<and> valid b"
                using exi_redir t0 by force
              then have c: "\<not> probe_line ?redir_ca (fst i)"
                unfolding probe_line_def by blast
              let ?r_line = "replace_policy ?redir_ca"
              have t3: "?r_line \<in> ?redir_ca"
                unfolding replace_policy_def
                using caE_init ca_set_nonempty exi_redir some_in_eq t2 by blast
              then have tag_diff: "ca_tag ?r_line \<noteq> tag (fst i)"
                using exi_redir setowned t0 by force
              let ?r_line' = "replace_line ?r_line (fst i)"
              have tag_same: "ca_tag ?r_line' = tag (fst i)"
                unfolding replace_line_def by simp
              let ?newset = "insert ?r_line' (?redir_ca - {?r_line})"
              have t4: "?r_line' \<notin> ?redir_ca"
                by (metis (full_types) exi_redir setowned t0 tag_same)
              then have "?newset \<inter> ?redir_ca = ?redir_ca - {?r_line}"
                by auto
              then have re: "card (?newset \<inter> ?redir_ca) = card ?redir_ca - 1"
                using caE_init ca_set_finite exi_redir subsetD t2 t3 by fastforce
              have "sa_read s0 (fst i) = {s0\<lparr>sram := list_update (sram s0) ?redir_set ?newset\<rparr>}"
                unfolding sa_read_def Let_def using c by auto
              then have "the_elem (sa_read s0 (fst i)) = s0\<lparr>sram := list_update (sram s0) ?redir_set ?newset\<rparr>"
                unfolding the_elem_def by auto
              then have "(sram (the_elem (sa_read s0 (fst i))))!?redir_set = ?newset"
                using exi_redir by simp
              then show ?thesis
                using re by simp
            }
          qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed

lemma remain_same:
  "\<forall>i \<in> mem_req cache_comp. \<forall>s0 \<in> state_E. \<forall>l \<noteq> the ((maps s0) (index (fst i))). (sram s0)!l = (sram (the_elem (sa_read s0 (fst i))))!l"
  proof -
    {
      fix i assume t0: "i \<in> mem_req cache_comp"
      have "\<forall>s0 \<in> state_E. \<forall>l \<noteq> the ((maps s0) (index (fst i))). (sram s0)!l = (sram (the_elem (sa_read s0 (fst i))))!l"
      proof -
        {
          fix s0 assume t1: "s0 \<in> state_E"
          have "\<forall>l \<noteq> the ((maps s0) (index (fst i))). (sram s0)!l = (sram (the_elem (sa_read s0 (fst i))))!l"
          proof -
            {
              fix l assume t2: "l \<noteq> the ((maps s0) (index (fst i)))"
              have "(sram s0)!l = (sram (the_elem (sa_read s0 (fst i))))!l"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (index (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_E_init unfolding state_E_witness_def using mem_mapping
                    by (smt caE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t1)
                  let ?redir_ca = "(sram s0) ! ?redir_set"
                  have "sram s0 \<in> ca_E cache_comp"
                    using state_E_init unfolding state_E_witness_def
                    proof -
                      assume "state_E = {t. \<exists>c\<in>ca_E cache_comp. t = \<lparr>sram = c, maps = map_conf cache_comp\<rparr>}"
                      then have "state_E = {s. \<exists>Cs. Cs \<in> ca_E cache_comp \<and> s = \<lparr>sram = Cs, maps = map_conf cache_comp\<rparr>}"
                        by (simp add: Bex_def_raw)
                      then have "\<exists>Cs. Cs \<in> ca_E cache_comp \<and> s0 = \<lparr>sram = Cs, maps = map_conf cache_comp\<rparr>"
                        using t1 by blast
                      then show ?thesis
                        by force
                    qed
                  then have setowned: "\<forall>i \<in> (mem_req cache_comp). \<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). tag (fst i) \<noteq> ca_tag e"
                    using mem_occupy by auto
                  then have "\<nexists>b. b \<in> ?redir_ca \<and> ca_tag b = tag (fst i) \<and> valid b"
                      using exi_redir t0 by force
                  then have c: "\<not> probe_line ?redir_ca (fst i)"
                    unfolding probe_line_def by blast
                  let ?r_line = "replace_policy ?redir_ca"
                  let ?newset = "insert (replace_line ?r_line (fst i)) (?redir_ca - {?r_line})"
                  have "sa_read s0 (fst i) = {s0\<lparr>sram := list_update (sram s0) ?redir_set ?newset\<rparr>}"
                    unfolding sa_read_def Let_def using c by auto
                  then show ?thesis using t2
                    by auto
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


subsection \<open>Proofs of Security Model\<close>

lemma read_not_zero:
  "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d = 1"
  using mem_cache_miss unfolding execution_def
  by auto

lemma read_not_uniform:
  assumes mem_len: "card (mem_req cache_comp) > 1"
    shows "\<forall>e. \<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
            snd d \<noteq> folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
  proof -
    {
      show ?thesis using mem_len
      proof -
        {
          fix e
          have "\<forall>mr \<in> mem_req cache_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
                 snd d \<noteq> folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
          proof -
            {
              fix mr assume t0: "mr \<in> mem_req cache_comp"
              have "\<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
                     snd d \<noteq> folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
              proof -
                {
                  fix s assume t1: "s \<in> state_E"
                  have "\<forall>d \<in> execution (fst mr) s e.
                         snd d \<noteq> folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
                  proof -
                    {
                      fix d assume t2: "d \<in> execution (fst mr) s e"
                      have emr: "execution (fst mr) s e = {((the ((maps s) (index (fst mr))), Miss), 1)}"
                        unfolding execution_def using mem_cache_miss
                        using t0 t1 by blast
                      then have valued: "d = ((the ((maps s) (index (fst mr))), Miss), 1)"
                        using t2 by blast
                      have exi_redir: "the ((maps s) (index (fst mr))) < length (sram s)"
                        using state_E_init unfolding state_E_witness_def using mem_mapping
                        by (smt caE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subset_eq t0 t1)
                      have "\<exists>m \<in> mem_req cache_comp. m \<noteq> mr"
                        using mem_len by (metis dual_order.strict_implies_not_eq inputdist_nonempty is_singletonI' is_singleton_altdef)
                      then obtain m where am: "m \<in> mem_req cache_comp \<and> m \<noteq> mr" by auto
                      then have em: "execution (fst m) s e = {((the ((maps s) (index (fst m))), Miss), 1)}"
                        unfolding execution_def using mem_cache_miss t1 by blast
                      have diff: "the ((maps s) (index (fst m))) \<noteq> the ((maps s) (index (fst mr)))"
                        using mem_mapping map_diff
                        by (smt am mem_Collect_eq mem_unique state.ext_inject state.surjective state_E_init state_E_witness_def t0 t1)
                      have makedist_m: "((fst m, (the ((maps s) (index (fst m))), Miss)), snd m) \<in> makeDist s e"
                        unfolding makeDist_def using am em by auto
                      have makedist_msub: "((fst m, (the ((maps s) (index (fst m))), Miss)), snd m) \<in>
                                          {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}"
                        using diff makedist_m valued by auto
                      have makedist_msub_value: "snd m > 0"
                        using inputdist_positive am by blast 
                      have makedist_msub_finite: "finite {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}"
                        using jodist_finite stateE_subset t1 by auto 
                      have makedist_msub_nonempty: "{u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)} \<noteq> {}"
                        using makedist_msub by blast
                      have makedist_msub_e: "\<forall>u \<in> {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}. snd u \<ge> 0"
                        using jodist_positive stateE_subset t1 by fastforce 
                      have makedist_msub_ne: "folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)} > 0"
                        using folds_plus_non_negative2[where ?P = "snd" and
                                                             ?w = "{u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}" and
                                                             ?d = "((fst m, (the ((maps s) (index (fst m))), Miss)), snd m)"]
                              makedist_msub_finite makedist_msub_nonempty makedist_msub_e
                              makedist_msub makedist_msub_value by auto
                      have makedist_sum: "folds (\<lambda>t p. snd t + p) 0 (makeDist s e) = 1"
                        using jodist_sum_one stateE_subset t1 by blast
                      have makedist_sub: "makeDist s e = {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)} \<union>
                                         {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}"
                        by auto
                      have makedist_sub_dis: "{u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)} \<inter>
                                              {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)} = {}"
                        by auto
                      have makedist_msub_finite2: "finite {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)}"
                        using jodist_finite stateE_subset t1 by auto
                      have makedist_sub_sum: "folds (\<lambda>t p. snd t + p) 0 ({u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)} \<union>
                                                                         {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}) = 
                                              folds (\<lambda>t p. snd t + p) (folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)}) 
                                              {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}"
                        using plus_comp_fun_commute_P.fold_set_union_disj[where ?P = "snd" and
                                                                                ?A = "{u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)}" and
                                                                                ?B = "{u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}" and
                                                                                ?z = 0]
                        using makedist_msub_finite makedist_msub_finite2 makedist_sub_dis by auto
                      have "folds (\<lambda>t p. snd t + p) (folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)}) 
                            {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)} = 
                            folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)} +
                            folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}"
                        proof -
                          have "\<forall>r ra P. r + folds (\<lambda>p. (+) (snd (p::(memory_request \<times> nat \<times> cachehit) \<times> real))) ra P = folds (\<lambda>p. (+) (snd p)) (r + ra) P \<or> infinite P"
                            by (metis (no_types) plus_comp_fun_commute_P.fold_fun_left_comm snd_conv)
                          then show ?thesis
                            by (smt makedist_msub_finite)
                        qed
                      then have "folds (\<lambda>t p. snd t + p) 0 (makeDist s e) =
                                 folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)} +
                                 folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) \<noteq> (the ((maps s) (index (fst mr))), Miss)}"
                        using makedist_sub makedist_sub_sum by presburger
                      then have "folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = (the ((maps s) (index (fst mr))), Miss)} < 1"
                        using makedist_sum makedist_msub_ne by linarith
                      then have ?thesis
                        using emr by auto
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

end
