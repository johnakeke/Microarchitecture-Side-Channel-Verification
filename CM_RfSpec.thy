section \<open>Random Fill TLB\<close>

theory CM_RfSpec
  imports Main CM_SecurityModel
begin

subsection \<open>Data type, Basic components\<close>

(*Basic data structures*)
type_synonym vaddr = nat
type_synonym setindex = nat
type_synonym wayindex = nat

datatype tlbhit = Hit | Miss

datatype event = RF_SEARCH

(*Memory blocks*)
record memory_request =
  va :: vaddr
  protect :: bool

(*TLB structure*)
record tlb_line =
  tlb_va :: vaddr
  tlb_set :: setindex
  tlb_way :: wayindex
  valid :: bool
  lock :: bool

type_synonym tlb = "(tlb_line set) list"

type_synonym mapping = "vaddr \<rightharpoonup> setindex"

(*State Machine*)
record state =
  sram :: tlb
  maps :: mapping

subsection \<open>Random Fill TLB model specifications\<close>

definition replace_policy :: "tlb_line set \<Rightarrow> tlb_line"
  where "replace_policy cs \<equiv> SOME l. l \<in> cs"

definition probe_line :: "tlb_line set \<Rightarrow> memory_request \<Rightarrow> bool"
  where "probe_line cs mr \<equiv> \<exists>b. b \<in> cs \<and> tlb_va b = va mr \<and> valid b"

definition replace_line :: "tlb_line \<Rightarrow> memory_request \<Rightarrow> tlb_line"
  where "replace_line cl mr \<equiv> cl\<lparr>tlb_va := va mr, valid := True, lock := protect mr\<rparr>"

definition rf_search :: "state \<Rightarrow> memory_request \<Rightarrow> memory_request set \<Rightarrow> state set" where
  "rf_search s mr mrs \<equiv>
      let redir_set = the ((maps s) (va mr));
          redir_tb = (sram s) ! redir_set in
      if probe_line redir_tb mr then {s}
      else let r_line = replace_policy redir_tb;
               mm_sec = {t. t \<in> mrs \<and> protect t}; mm_nonsec = {t. t \<in> mrs \<and> \<not> protect t} in
        if protect mr then
          {t. \<exists>mm \<in> mm_sec. let mm_set = the ((maps s) (va mm)); mm_tb = (sram s) ! mm_set; r'_line = replace_policy mm_tb;
                                newset = insert (replace_line r'_line mm) (mm_tb - {r'_line}) in
              t = s\<lparr>sram := list_update (sram s) mm_set newset\<rparr>}
        else
          if lock r_line then
            {t. \<exists>mm \<in> mm_nonsec. let mm_set = the ((maps s) (va mm)); mm_tb = (sram s) ! mm_set; r'_line = replace_policy mm_tb;
                                  newset = insert (replace_line r'_line mm) (mm_tb - {r'_line}) in
                t = s\<lparr>sram := list_update (sram s) mm_set newset\<rparr>}
          else let newset = insert (replace_line r_line mr) (redir_tb - {r_line}) in
               {s\<lparr>sram := list_update (sram s) redir_set newset\<rparr>}"


subsection \<open>Instantiation\<close>

record tlb_NE =
  tlb_N :: "tlb set"
  tlb_E :: "tlb set"
  map_conf :: "mapping"
  mem_req :: "(memory_request \<times> real) set"

consts tlb_comp :: tlb_NE

definition tlb_comp_witness :: "tlb_NE"
  where "tlb_comp_witness \<equiv> \<lparr>tlb_N = {[{(\<lparr>tlb_va = 1, tlb_set = 0, tlb_way = 0, valid = True, lock = False\<rparr>)}]},
                             tlb_E = {[{(\<lparr>tlb_va = 1, tlb_set = 0, tlb_way = 0, valid = True, lock = False\<rparr>)}]},
                             map_conf = (\<lambda>t. if t = 0 then Some 0 else None),
                             mem_req = {(\<lparr>va = 0, protect = True\<rparr>, 1)}\<rparr>"

specification (tlb_comp)
  tlbN_finite: "finite (tlb_N tlb_comp)"
  tlbN_nonempty: "(tlb_N tlb_comp) \<noteq> {}"

  tlb_length: "\<forall>c \<in> (tlb_N tlb_comp). length c > 0"
  tlb_length2: "\<forall>c1 c2. c1 \<in> (tlb_N tlb_comp) \<and> c2 \<in> (tlb_N tlb_comp) \<and> c1 \<noteq> c2 \<longrightarrow> length c1 = length c2"
  tlb_finite: "\<forall>c \<in> (tlb_N tlb_comp). finite (set c)"
  tlb_set_nonempty: "\<forall>c \<in> (tlb_N tlb_comp). (\<forall>l < length c. c!l \<noteq> {})"
  tlb_set_finite: "\<forall>c \<in> (tlb_N tlb_comp). (\<forall>l < length c. finite (c!l))"
  tlb_set_num: "\<forall>c \<in> (tlb_N tlb_comp). (\<forall>l < length c. \<forall>e \<in> (c!l). tlb_set e = l)"
  tlb_way_num: "\<forall>c \<in> (tlb_N tlb_comp). (\<forall>l1 l2. l1 < length c \<and> l2 < length c \<and> l1 \<noteq> l2 \<longrightarrow> card(c!l1) = card(c!l2))"
  tlb_way_num2: "\<forall>c \<in> (tlb_N tlb_comp). (\<forall>l < length c. \<forall>e1 e2. e1 \<in> (c!l) \<and> e2 \<in> (c!l) \<and> e1 \<noteq> e2 \<longrightarrow> tlb_way e1 \<noteq> tlb_way e2)"

  tlbE_init: "(tlb_E tlb_comp) \<subseteq> (tlb_N tlb_comp)"
  tlbE_nonempty: "(tlb_E tlb_comp) \<noteq> {}"

  map_range: "\<forall>c \<in> (tlb_N tlb_comp). (\<forall>i. (map_conf tlb_comp) i \<noteq> None \<longrightarrow> the ((map_conf tlb_comp) i) < length c)"
  map_diff: "\<forall>i j. i \<noteq> j \<and> (map_conf tlb_comp) i \<noteq> None \<and> (map_conf tlb_comp) j \<noteq> None \<longrightarrow> the ((map_conf tlb_comp) i) \<noteq> the ((map_conf tlb_comp) j)"
  
  mem_finite: "finite (mem_req tlb_comp)"
  mem_nonempty: "card (mem_req tlb_comp) > 0"
  mem_unique: "\<forall>i j. i \<in> (mem_req tlb_comp) \<and> j \<in> (mem_req tlb_comp) \<and> i \<noteq> j \<longrightarrow> va (fst i) \<noteq> va (fst j)"
  mem_positive: "\<forall>i \<in> (mem_req tlb_comp). snd i > 0"
  mem_sum_one: "folds (\<lambda>t p. snd t + p) 0 (mem_req tlb_comp) = 1"
  mem_length: "\<forall>c \<in> (tlb_N tlb_comp). card (mem_req tlb_comp) \<le> length c"
  mem_occupy: "\<forall>i \<in> (mem_req tlb_comp). \<forall>c \<in> (tlb_E tlb_comp). \<forall>l < length c. \<forall>e \<in> (c!l). va (fst i) \<noteq> tlb_va e"
  mem_protect: "\<forall>i \<in> (mem_req tlb_comp). protect (fst i)"
  mem_mapping: "\<forall>i \<in> (mem_req tlb_comp). (map_conf tlb_comp) (va (fst i)) \<noteq> None"
  apply(intro exI[of _ tlb_comp_witness])
  unfolding tlb_comp_witness_def by auto

(*state N*)
consts state_N :: "state set"

definition state_N_witness :: "state set"
  where "state_N_witness \<equiv> {t. \<exists>c \<in> (tlb_N tlb_comp). t = \<lparr>sram = c, maps = (map_conf tlb_comp)\<rparr>}"

specification (state_N)
  state_N_init: "state_N = state_N_witness"
  by simp

lemma stateN_finite: "finite state_N"
  proof -
    {
      have "\<forall>c \<in> (tlb_N tlb_comp). finite {t. \<exists>c \<in> (tlb_N tlb_comp). t = \<lparr>sram = c, maps = (map_conf tlb_comp)\<rparr>}"
        using tlbN_finite by auto
      then show ?thesis
        using state_N_init state_N_witness_def by auto 
    }
  qed

lemma stateN_nonempty: "state_N \<noteq> {}"
  using state_N_init state_N_witness_def tlbN_nonempty
  by blast

(*state E*)
consts state_E :: "state set"

definition state_E_witness :: "state set"
  where "state_E_witness \<equiv> {t. \<exists>c \<in> (tlb_E tlb_comp). t = \<lparr>sram = c, maps = (map_conf tlb_comp)\<rparr>}"

specification (state_E)
  state_E_init: "state_E = state_E_witness"
  by simp

lemma stateE_nonempty: "state_E \<noteq> {}"
  using state_E_init state_E_witness_def tlbE_nonempty
  by blast

lemma stateE_subset: "state_E \<subseteq> state_N"
  using state_N_init state_N_witness_def state_E_init state_E_witness_def
  by (smt Collect_mono_iff tlbE_init subset_eq)

lemma image_card:
  assumes a0: "finite A"
      and a1: "A \<noteq> {}"
      and a2: "\<forall>i j. i \<in> A \<and> j \<in> A \<and> i \<noteq> j \<longrightarrow> P i \<noteq> P j"
    shows "card A = card (P ` A)"
proof -
  {
    show ?thesis using a0 a1 a2
    proof(induct rule: finite_ne_induct)
      case (singleton x)
      then show ?case by auto
    next
      case (insert x F)
      have "P ` (insert x F) = {P x} \<union> (P ` F)"
        by blast
      moreover have "P x \<notin> P ` F"
        using insert.hyps(3) insert.prems by auto
      ultimately show ?case
        by (simp add: insert.hyps(1) insert.hyps(3) insert.hyps(4) insert.prems) 
    qed
  }
qed

(*Observation*)
definition rf_search_observe :: "state \<Rightarrow> memory_request \<Rightarrow> memory_request set \<Rightarrow> ((setindex \<times> tlbhit) \<times> real) set" where
  "rf_search_observe s mr mrs \<equiv>
      let redir_set = the ((maps s) (va mr));
          redir_tb = (sram s) ! redir_set in
      if probe_line redir_tb mr then {((redir_set, Hit), 1)}
      else let r_line = replace_policy redir_tb;
               mm_sec = {t. t \<in> mrs \<and> protect t}; mm_nonsec = {t. t \<in> mrs \<and> \<not> protect t} in
        if protect mr then
          {t. \<exists>mm \<in> mm_sec. let mm_set = the ((maps s) (va mm)) in
              t = ((mm_set, Miss), 1/card mm_sec)}
        else
          if lock r_line then
            {t. \<exists>mm \<in> mm_nonsec. let mm_set = the ((maps s) (va mm)) in
                t = ((mm_set, Miss), 1/card mm_nonsec)}
          else
            {((redir_set, Miss), 1)}"

lemma mem_tlb_miss:
  "\<forall>i \<in> mem_req tlb_comp. \<forall>s0 \<in> state_E. rf_search_observe s0 (fst i) (fst ` (mem_req tlb_comp)) =
    {t. \<exists>r \<in> mem_req tlb_comp. let r_set = the ((maps s0) (va (fst r))) in
        t = ((r_set, Miss), 1/card (mem_req tlb_comp))}"
  proof -
    {
      fix i assume t0: "i \<in> mem_req tlb_comp"
      have "\<forall>s0 \<in> state_E. rf_search_observe s0 (fst i) (fst ` (mem_req tlb_comp)) =
            {t. \<exists>r \<in> mem_req tlb_comp. let r_set = the ((maps s0) (va (fst r))) in
                t = ((r_set, Miss), 1/card (mem_req tlb_comp))}"
      proof -
        {
          fix s0 assume t1: "s0 \<in> state_E"
          have "rf_search_observe s0 (fst i) (fst ` (mem_req tlb_comp)) =
                {t. \<exists>r \<in> mem_req tlb_comp. let r_set = the ((maps s0) (va (fst r))) in
                    t = ((r_set, Miss), 1/card (mem_req tlb_comp))}"
          proof -
            {
              let ?redir_set = "the ((maps s0) (va (fst i)))"
              have exi_redir: "?redir_set < length (sram s0)"
                using state_E_init unfolding state_E_witness_def using mem_mapping
                by (smt tlbE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t1)
              let ?redir_tb = "(sram s0) ! ?redir_set"
              have t2: "sram s0 \<in> tlb_E tlb_comp"
                using state_E_init unfolding state_E_witness_def
                proof -
                  assume "state_E = {t. \<exists>c\<in>tlb_E tlb_comp. t = \<lparr>sram = c, maps = map_conf tlb_comp\<rparr>}"
                  then have "state_E = {s. \<exists>Ts. Ts \<in> tlb_E tlb_comp \<and> s = \<lparr>sram = Ts, maps = map_conf tlb_comp\<rparr>}"
                    by meson
                  then have "\<exists>Ts. Ts \<in> tlb_E tlb_comp \<and> s0 = \<lparr>sram = Ts, maps = map_conf tlb_comp\<rparr>"
                    using t1 by blast
                  then show ?thesis
                    by force
                qed
              then have setowned: "\<forall>i \<in> (mem_req tlb_comp). \<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). va (fst i) \<noteq> tlb_va e"
                using mem_occupy by auto
              then have "\<nexists>b. b \<in> ?redir_tb \<and> tlb_va b = va (fst i) \<and> valid b"
                using exi_redir t0 by force
              then have c1: "\<not> probe_line ?redir_tb (fst i)"
                unfolding probe_line_def by blast
              let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
              have c2: "protect (fst i)"
                by (simp add: mem_protect t0)
              have out1: "rf_search_observe s0 (fst i) (fst ` (mem_req tlb_comp)) =
                         {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)) in
                             t = ((mm_set, Miss), 1/card ?mm_sec)}"
                unfolding rf_search_observe_def Let_def
                using c1 c2 by simp
              have "?mm_sec = fst ` (mem_req tlb_comp)"
                using mem_protect by blast
              then have out2: "rf_search_observe s0 (fst i) (fst ` (mem_req tlb_comp)) =
                              {t. \<exists>mm \<in> fst ` (mem_req tlb_comp). let mm_set = the ((maps s0) (va mm)) in
                                  t = ((mm_set, Miss), 1/card (fst ` (mem_req tlb_comp)))}"
                using out1 by auto
              have "card (fst ` (mem_req tlb_comp)) = card (mem_req tlb_comp)"
                using image_card mem_finite mem_nonempty mem_unique
                proof -
                  have "mem_req tlb_comp \<noteq> {}"
                    using t0 by force
                  then show ?thesis
                    by (metis (no_types) image_card mem_finite mem_unique)
                qed
              then have out3: "rf_search_observe s0 (fst i) (fst ` (mem_req tlb_comp)) =
                              {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                  t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                using out2 by auto
              then show ?thesis by blast 
            }
          qed
        }
        then show ?thesis by blast
      qed
    }
    then show ?thesis by blast
  qed

(*pmf instantiate*)
definition execution :: "memory_request \<Rightarrow> state \<Rightarrow> event \<Rightarrow> ((setindex \<times> tlbhit) \<times> real) set"
  where "execution mr s e \<equiv> rf_search_observe s mr (fst ` (mem_req tlb_comp))"

lemma search_finite:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. finite (execution (fst mr) s e)"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. finite (execution (fst mr) s e)"
      proof -
        {
          fix i assume t0: "i \<in> mem_req tlb_comp"
          have "\<forall>s0 \<in> state_N. finite (execution (fst i) s0 e)"
          proof -
            {
              fix s0 assume t1: "s0 \<in> state_N"
              have "finite (execution (fst i) s0 e)"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (va (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_N_init unfolding state_N_witness_def using mem_mapping
                    by (smt map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
                  let ?redir_tb = "(sram s0) ! ?redir_set"
                  show ?thesis
                  proof(cases "probe_line ?redir_tb (fst i)")
                    case True
                    then have "execution (fst i) s0 e = {((?redir_set, Hit), 1)}"
                      unfolding execution_def rf_search_observe_def Let_def by auto
                    then show ?thesis by simp 
                  next
                    case False
                    let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
                    have c2: "protect (fst i)"
                      by (simp add: mem_protect t0)
                    have out1: "execution (fst i) s0 e =
                               {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)) in
                                   t = ((mm_set, Miss), 1/card ?mm_sec)}"
                      unfolding execution_def rf_search_observe_def Let_def
                      using False c2 by simp
                    have "?mm_sec = fst ` (mem_req tlb_comp)"
                      using mem_protect by blast
                    then have out2: "execution (fst i) s0 e =
                                    {t. \<exists>mm \<in> fst ` (mem_req tlb_comp). let mm_set = the ((maps s0) (va mm)) in
                                        t = ((mm_set, Miss), 1/card (fst ` (mem_req tlb_comp)))}"
                      using out1 by auto
                    have "card (fst ` (mem_req tlb_comp)) = card (mem_req tlb_comp)"
                      using image_card mem_finite mem_nonempty mem_unique
                      proof -
                        have "mem_req tlb_comp \<noteq> {}"
                          using t0 by force
                        then show ?thesis
                          by (metis (no_types) image_card mem_finite mem_unique)
                      qed
                    then have out3: "execution (fst i) s0 e =
                                      {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                          t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using out2 by auto
                    have "finite {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                     t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using mem_finite by auto
                    then show ?thesis using out3 by auto
                  qed
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

lemma search_nonempty:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. execution (fst mr) s e \<noteq> {}"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. execution (fst mr) s e \<noteq> {}"
      proof -
        {
          fix i assume t0: "i \<in> mem_req tlb_comp"
          have "\<forall>s0 \<in> state_N. execution (fst i) s0 e \<noteq> {}"
          proof -
            {
              fix s0 assume t1: "s0 \<in> state_N"
              have "execution (fst i) s0 e \<noteq> {}"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (va (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_N_init unfolding state_N_witness_def using mem_mapping
                    by (smt map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
                  let ?redir_tb = "(sram s0) ! ?redir_set"
                  show ?thesis
                  proof(cases "probe_line ?redir_tb (fst i)")
                    case True
                    then have "execution (fst i) s0 e = {((?redir_set, Hit), 1)}"
                      unfolding execution_def rf_search_observe_def Let_def by auto
                    then show ?thesis by simp 
                  next
                    case False
                    let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
                    have c2: "protect (fst i)"
                      by (simp add: mem_protect t0)
                    have out1: "execution (fst i) s0 e =
                               {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)) in
                                   t = ((mm_set, Miss), 1/card ?mm_sec)}"
                      unfolding execution_def rf_search_observe_def Let_def
                      using False c2 by simp
                    have "?mm_sec = fst ` (mem_req tlb_comp)"
                      using mem_protect by blast
                    then have out2: "execution (fst i) s0 e =
                                    {t. \<exists>mm \<in> fst ` (mem_req tlb_comp). let mm_set = the ((maps s0) (va mm)) in
                                        t = ((mm_set, Miss), 1/card (fst ` (mem_req tlb_comp)))}"
                      using out1 by auto
                    have "card (fst ` (mem_req tlb_comp)) = card (mem_req tlb_comp)"
                      using image_card mem_finite mem_nonempty mem_unique
                      proof -
                        have "mem_req tlb_comp \<noteq> {}"
                          using t0 by force
                        then show ?thesis
                          by (metis (no_types) image_card mem_finite mem_unique)
                      qed
                    then have out3: "execution (fst i) s0 e =
                                      {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                          t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using out2 by auto
                    have "mem_req tlb_comp \<noteq> {}"
                      using t0 by blast
                    then have "{t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                   t = ((mm_set, Miss), 1/card (mem_req tlb_comp))} \<noteq> {}"
                      by auto
                    then show ?thesis using out3 by auto
                  qed
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

lemma search_unique:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. \<forall>m n. m \<in> (execution (fst mr) s e) \<and> n \<in> (execution (fst mr) s e) \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. \<forall>m n. m \<in> (execution (fst mr) s e) \<and> n \<in> (execution (fst mr) s e) \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n"
      proof -
        {
          fix i assume t0: "i \<in> mem_req tlb_comp"
          have "\<forall>s0 \<in> state_N. \<forall>m n. m \<in> (execution (fst i) s0 e) \<and> n \<in> (execution (fst i) s0 e) \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n"
          proof -
            {
              fix s0 assume t1: "s0 \<in> state_N"
              have "\<forall>m n. m \<in> (execution (fst i) s0 e) \<and> n \<in> (execution (fst i) s0 e) \<and> m \<noteq> n \<longrightarrow> fst m \<noteq> fst n"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (va (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_N_init unfolding state_N_witness_def using mem_mapping
                    by (smt map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
                  let ?redir_tb = "(sram s0) ! ?redir_set"
                  show ?thesis
                  proof(cases "probe_line ?redir_tb (fst i)")
                    case True
                    then have "execution (fst i) s0 e = {((?redir_set, Hit), 1)}"
                      unfolding execution_def rf_search_observe_def Let_def by auto
                    then show ?thesis by simp 
                  next
                    case False
                    let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
                    have c2: "protect (fst i)"
                      by (simp add: mem_protect t0)
                    have out1: "execution (fst i) s0 e =
                               {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)) in
                                   t = ((mm_set, Miss), 1/card ?mm_sec)}"
                      unfolding execution_def rf_search_observe_def Let_def
                      using False c2 by simp
                    have "?mm_sec = fst ` (mem_req tlb_comp)"
                      using mem_protect by blast
                    then have out2: "execution (fst i) s0 e =
                                    {t. \<exists>mm \<in> fst ` (mem_req tlb_comp). let mm_set = the ((maps s0) (va mm)) in
                                        t = ((mm_set, Miss), 1/card (fst ` (mem_req tlb_comp)))}"
                      using out1 by auto
                    have "card (fst ` (mem_req tlb_comp)) = card (mem_req tlb_comp)"
                      using image_card mem_finite mem_nonempty mem_unique
                      proof -
                        have "mem_req tlb_comp \<noteq> {}"
                          using t0 by force
                        then show ?thesis
                          by (metis (no_types) image_card mem_finite mem_unique)
                      qed
                    then have out3: "execution (fst i) s0 e =
                                      {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                          t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using out2 by auto
                    then show ?thesis by auto
                  qed
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

lemma search_positive:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. \<forall>d \<in> (execution (fst mr) s e). snd d \<ge> 0"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. \<forall>d \<in> (execution (fst mr) s e). snd d \<ge> 0"
      proof -
        {
          fix i assume t0: "i \<in> mem_req tlb_comp"
          have "\<forall>s0 \<in> state_N. \<forall>d \<in> (execution (fst i) s0 e). snd d \<ge> 0"
          proof -
            {
              fix s0 assume t1: "s0 \<in> state_N"
              have "\<forall>d \<in> (execution (fst i) s0 e). snd d \<ge> 0"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (va (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_N_init unfolding state_N_witness_def using mem_mapping
                    by (smt map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
                  let ?redir_tb = "(sram s0) ! ?redir_set"
                  show ?thesis
                  proof(cases "probe_line ?redir_tb (fst i)")
                    case True
                    then have "execution (fst i) s0 e = {((?redir_set, Hit), 1)}"
                      unfolding execution_def rf_search_observe_def Let_def by auto
                    then show ?thesis by simp 
                  next
                    case False
                    let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
                    have c2: "protect (fst i)"
                      by (simp add: mem_protect t0)
                    have out1: "execution (fst i) s0 e =
                               {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)) in
                                   t = ((mm_set, Miss), 1/card ?mm_sec)}"
                      unfolding execution_def rf_search_observe_def Let_def
                      using False c2 by simp
                    have "?mm_sec = fst ` (mem_req tlb_comp)"
                      using mem_protect by blast
                    then have out2: "execution (fst i) s0 e =
                                    {t. \<exists>mm \<in> fst ` (mem_req tlb_comp). let mm_set = the ((maps s0) (va mm)) in
                                        t = ((mm_set, Miss), 1/card (fst ` (mem_req tlb_comp)))}"
                      using out1 by auto
                    have "card (fst ` (mem_req tlb_comp)) = card (mem_req tlb_comp)"
                      using image_card mem_finite mem_nonempty mem_unique
                      proof -
                        have "mem_req tlb_comp \<noteq> {}"
                          using t0 by force
                        then show ?thesis
                          by (metis (no_types) image_card mem_finite mem_unique)
                      qed
                    then have out3: "execution (fst i) s0 e =
                                      {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                          t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using out2 by auto
                    then show ?thesis by auto
                  qed
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

lemma set_size:
  assumes a_finite: "finite (w::((nat \<times> tlbhit) \<times> real) set)"
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

lemma set_size2:
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

lemma search_sum_one:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst mr) s e) = 1"
      proof -
        {
          fix i assume t0: "i \<in> mem_req tlb_comp"
          have "\<forall>s0 \<in> state_N. folds (\<lambda>t p. snd t + p) 0 (execution (fst i) s0 e) = 1"
          proof -
            {
              fix s0 assume t1: "s0 \<in> state_N"
              have "folds (\<lambda>t p. snd t + p) 0 (execution (fst i) s0 e) = 1"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (va (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_N_init unfolding state_N_witness_def using mem_mapping
                    by (smt map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) t0 t1)
                  let ?redir_tb = "(sram s0) ! ?redir_set"
                  show ?thesis
                  proof(cases "probe_line ?redir_tb (fst i)")
                    case True
                    then have "execution (fst i) s0 e = {((?redir_set, Hit), 1)}"
                      unfolding execution_def rf_search_observe_def Let_def by auto
                    then show ?thesis by simp 
                  next
                    case False
                    let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
                    have c2: "protect (fst i)"
                      by (simp add: mem_protect t0)
                    have out1: "execution (fst i) s0 e =
                               {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)) in
                                   t = ((mm_set, Miss), 1/card ?mm_sec)}"
                      unfolding execution_def rf_search_observe_def Let_def
                      using False c2 by simp
                    have "?mm_sec = fst ` (mem_req tlb_comp)"
                      using mem_protect by blast
                    then have out2: "execution (fst i) s0 e =
                                    {t. \<exists>mm \<in> fst ` (mem_req tlb_comp). let mm_set = the ((maps s0) (va mm)) in
                                        t = ((mm_set, Miss), 1/card (fst ` (mem_req tlb_comp)))}"
                      using out1 by auto
                    have "card (fst ` (mem_req tlb_comp)) = card (mem_req tlb_comp)"
                      using image_card mem_finite mem_nonempty mem_unique
                      proof -
                        have "mem_req tlb_comp \<noteq> {}"
                          using t0 by force
                        then show ?thesis
                          by (metis (no_types) image_card mem_finite mem_unique)
                      qed
                    then have out3: "execution (fst i) s0 e =
                                      {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                          t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using out2 by auto
                    have "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                                        t = ((mm_set, Miss), 1/card (mem_req tlb_comp))} =
                         1/card (mem_req tlb_comp) * card {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                                              t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}"
                      using set_size[where ?w = "{t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                                     t = ((mm_set, Miss), 1/card (mem_req tlb_comp))}" and
                                           ?P = "snd" and
                                           ?i = "1/card (mem_req tlb_comp)"]
                            mem_finite mem_nonempty t0 by auto 
                    moreover have "card {t. \<exists>mm \<in> mem_req tlb_comp. let mm_set = the ((maps s0) (va (fst mm))) in
                                            t = ((mm_set, Miss), 1/card (mem_req tlb_comp))} =
                                   card (mem_req tlb_comp)"
                    proof -
                      {
                        have "\<forall>i1 i2. i1 \<in> mem_req tlb_comp \<and> i2 \<in> mem_req tlb_comp \<and> i1 \<noteq> i2 \<longrightarrow>
                                      ((the ((maps s0) (va (fst i1))), Miss), 1/card (mem_req tlb_comp)) \<noteq> ((the ((maps s0) (va (fst i2))), Miss), 1/card (mem_req tlb_comp))"
                          using mem_mapping mem_unique
                          by (smt Pair_inject map_diff mem_Collect_eq state.select_convs(2) state_N_init state_N_witness_def t1)
                        then  show ?thesis unfolding Let_def
                          using set_size2[where ?A = "mem_req tlb_comp" and
                                                ?f = "\<lambda>e. ((the ((maps s0) (va (fst e))), Miss), 1/card (mem_req tlb_comp))"]
                                mem_finite mem_nonempty by fastforce
                      }
                    qed
                    ultimately show ?thesis
                      by (simp add: mem_nonempty out3) 
                  qed
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

interpretation CM state_N state_E "mem_req tlb_comp" execution
  apply standard
  using mem_finite mem_nonempty mem_unique mem_positive mem_sum_one
        search_finite search_nonempty search_unique search_positive search_sum_one
        stateN_finite stateN_nonempty stateE_nonempty stateE_subset
  by auto

subsection \<open>Proofs of Correctness\<close>

lemma one_changed_remain_same:
  "\<forall>i \<in> mem_req tlb_comp. \<forall>s0 \<in> state_E. \<forall>s' \<in> rf_search s0 (fst i) (fst ` (mem_req tlb_comp)).
    \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
  proof -
    {
      fix i assume t0: "i \<in> mem_req tlb_comp"
      have "\<forall>s0 \<in> state_E. \<forall>s' \<in> rf_search s0 (fst i) (fst ` (mem_req tlb_comp)).
              \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
      proof -
        {
          fix s0 assume t1: "s0 \<in> state_E"
          have "\<forall>s' \<in> rf_search s0 (fst i) (fst ` (mem_req tlb_comp)).
                  \<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
          proof -
            {
              fix s' assume t2: "s' \<in> rf_search s0 (fst i) (fst ` (mem_req tlb_comp))"
              have "\<exists>!l. (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and> (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
              proof -
                {
                  let ?redir_set = "the ((maps s0) (va (fst i)))"
                  have exi_redir: "?redir_set < length (sram s0)"
                    using state_E_init unfolding state_E_witness_def using mem_mapping
                    by (smt tlbE_init map_range mem_Collect_eq state.select_convs(1) state.select_convs(2) subsetD t0 t1)
                  let ?redir_tb = "(sram s0) ! ?redir_set"
                  have t3: "sram s0 \<in> tlb_E tlb_comp"
                    using state_E_init unfolding state_E_witness_def
                    proof -
                      assume "state_E = {t. \<exists>c\<in>tlb_E tlb_comp. t = \<lparr>sram = c, maps = map_conf tlb_comp\<rparr>}"
                      then have "state_E = {s. \<exists>Ts. Ts \<in> tlb_E tlb_comp \<and> s = \<lparr>sram = Ts, maps = map_conf tlb_comp\<rparr>}"
                        by meson
                      then have "\<exists>Ts. Ts \<in> tlb_E tlb_comp \<and> s0 = \<lparr>sram = Ts, maps = map_conf tlb_comp\<rparr>"
                        using t1 by blast
                      then show ?thesis
                        by force
                    qed
                  then have setowned: "\<forall>i \<in> (mem_req tlb_comp). \<forall>l < length (sram s0). \<forall>e \<in> ((sram s0)!l). va (fst i) \<noteq> tlb_va e"
                    using mem_occupy by auto
                  then have "\<nexists>b. b \<in> ?redir_tb \<and> tlb_va b = va (fst i) \<and> valid b"
                    using exi_redir t0 by force
                  then have c1: "\<not> probe_line ?redir_tb (fst i)"
                    unfolding probe_line_def by blast
                  let ?mm_sec = "{t. t \<in> (fst ` (mem_req tlb_comp)) \<and> protect t}"
                  have c2: "protect (fst i)"
                    by (simp add: mem_protect t0)
                  have out: "rf_search s0 (fst i) (fst ` (mem_req tlb_comp)) =
                            {t. \<exists>mm \<in> ?mm_sec. let mm_set = the ((maps s0) (va mm)); mm_tb = (sram s0) ! mm_set; r'_line = replace_policy mm_tb;
                                                            newset = insert (replace_line r'_line mm) (mm_tb - {r'_line}) in
                                                t = s0\<lparr>sram := list_update (sram s0) mm_set newset\<rparr>}"
                    unfolding rf_search_def Let_def
                    using c1 c2 by simp
                  then have "\<exists>mm \<in> ?mm_sec.
                              s' = (let mm_set = the ((maps s0) (va mm)); mm_tb = (sram s0) ! mm_set; r'_line = replace_policy mm_tb;
                                                 newset = insert (replace_line r'_line mm) (mm_tb - {r'_line}) in
                                    s0\<lparr>sram := list_update (sram s0) mm_set newset\<rparr>)"
                    using t2 by (smt mem_Collect_eq)
                  then obtain mm where t4: "mm \<in> ?mm_sec \<and>
                                            s' = (let mm_set = the ((maps s0) (va mm)); mm_tb = (sram s0) ! mm_set; r'_line = replace_policy mm_tb;
                                                               newset = insert (replace_line r'_line mm) (mm_tb - {r'_line}) in
                                                  s0\<lparr>sram := list_update (sram s0) mm_set newset\<rparr>)"
                    by auto
                  let ?mm_set = "the ((maps s0) (va mm))"
                  have mm_length: "?mm_set < length (sram s0)"
                    using t4
                    proof -
                      have "state_E_witness = {s. \<exists>Ts. Ts \<in> tlb_E tlb_comp \<and> s = \<lparr>sram = Ts, maps = map_conf tlb_comp\<rparr>}"
                        by (simp add: Bex_def_raw state_E_witness_def)
                      then obtain TTs :: "state \<Rightarrow> tlb_line set list" where
                        f1: "TTs s0 \<in> tlb_E tlb_comp \<and> s0 = \<lparr>sram = TTs s0, maps = map_conf tlb_comp\<rparr>"
                        using state_E_init t1 by moura
                      then have f2: "\<lparr>sram = TTs s0, maps = map_conf tlb_comp\<rparr> = \<lparr>sram = sram s0, maps = maps s0, \<dots> = state.more s0\<rparr>"
                        by simp
                      have "map_conf tlb_comp (va mm) \<noteq> None"
                        using mem_mapping t4 by fastforce
                      then show ?thesis
                        using f2 f1 by (metis map_range state.ext_inject subsetD tlbE_init)
                    qed
                  let ?mm_tb = "(sram s0) ! ?mm_set"
                  let ?r'_line = "replace_policy ?mm_tb"
                  have r'_belong: "?r'_line \<in> ?mm_tb"
                    using t4
                    proof -
                      have "sram s0 \<in> tlb_N tlb_comp"
                        by (meson subsetD t3 tlbE_init)
                      then show ?thesis
                        by (simp add: mm_length replace_policy_def some_in_eq tlb_set_nonempty)
                    qed 
                  then have tag_diff: "tlb_va ?r'_line \<noteq> va mm"
                    using setowned mm_length t4 by fastforce 
                  let ?r'_line' = "replace_line ?r'_line mm"
                  have tag_same: "tlb_va ?r'_line' = va mm"
                    unfolding replace_line_def by simp
                  have t5: "?r'_line' \<notin> ?mm_tb"
                    proof -
                      have "mm \<in> fst ` mem_req tlb_comp"
                        using t4 by fastforce
                      then show ?thesis
                        by (metis (no_types) imageE mm_length setowned tag_same)
                    qed
                  let ?newset = "insert ?r'_line' (?mm_tb - {?r'_line})"
                  have "?newset \<inter> ?mm_tb = ?mm_tb - {?r'_line}"
                    using t5 by auto
                  then have re: "card (?newset \<inter> ?mm_tb) = card ?mm_tb - 1"
                    by (simp add: card_Diff_subset_Int r'_belong)
                  have out1: "s' = s0\<lparr>sram := list_update (sram s0) ?mm_set ?newset\<rparr>"
                    by (metis (full_types) t4)
                  then have "sram s' = list_update (sram s0) ?mm_set ?newset"
                    by auto
                  then have "\<exists>!l. l = ?mm_set \<and> (\<forall>l' \<noteq> l. (sram s0)!l' = (sram s')!l') \<and>
                                  (card (((sram s') ! l) \<inter> ((sram s0) ! l)) = card ((sram s0) ! l) - 1)"
                    using re mm_length nth_list_update_eq by auto 
                  then show ?thesis
                    by (metis \<open>sram s' = (sram s0) [the (maps s0 (va mm)) := insert (replace_line (replace_policy (sram s0 ! the (maps s0 (va mm)))) mm) (sram s0 ! the (maps s0 (va mm)) - {replace_policy (sram s0 ! the (maps s0 (va mm)))})]\<close> insertI1 mm_length nth_list_update_eq t5) 
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

lemma search_not_zero:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
      proof -
        {
          fix mr
          assume t0: "mr \<in> mem_req tlb_comp"
          have "\<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
          proof -
            {
              fix s
              assume t1: "s \<in> state_E"
              have "\<forall>d \<in> execution (fst mr) s e. snd d \<noteq> 0"
              proof -
                {
                  have "execution (fst mr) s e = {t. \<exists>r\<in>mem_req tlb_comp. let r_set = the (maps s (va (fst r))) in t = ((r_set, Miss), 1 / real (card (mem_req tlb_comp)))}"
                    unfolding execution_def using mem_tlb_miss t0 t1 by auto
                  then show ?thesis
                    using mem_nonempty by auto
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

lemma search_uniform:
  "\<forall>e. \<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
    snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
  proof -
    {
      fix e
      have "\<forall>mr \<in> mem_req tlb_comp. \<forall>s \<in> state_E. \<forall>d \<in> execution (fst mr) s e.
             snd d = folds (\<lambda>t p. snd t + p) 0 {u. u \<in> makeDist s e \<and> snd (fst u) = fst d}"
      proof -
        {
          fix mr assume t0: "mr \<in> mem_req tlb_comp"
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
                  have emr: "execution (fst mr) s e = {t. \<exists>r \<in> mem_req tlb_comp. let r_set = the ((maps s) (va (fst r))) in
                                                          t = ((r_set, Miss), 1/card (mem_req tlb_comp))}"
                    unfolding execution_def using mem_tlb_miss
                    using t0 t1 by blast
                  have pmf_m: "\<forall>m \<in> mem_req tlb_comp. \<exists>!t \<in> execution (fst m) s e. t = (fst d, snd d)"
                    using \<open>d \<in> execution (fst mr) s e\<close> execution_def mem_tlb_miss t0 t1 by auto
                  then have makedist_m: "\<forall>m \<in> mem_req tlb_comp. ((fst m, fst d), snd m * snd d) \<in> makeDist s e"
                    unfolding makeDist_def using emr by fastforce
                  then have set_equal: "{u. u \<in> makeDist s e \<and> snd (fst u) = fst d} =
                                        {t. \<exists>m \<in> mem_req tlb_comp. t = ((fst m, fst d), snd m * snd d)}"
                    by (smt Collect_cong Pair_inject execution_def makeDist_def mem_Collect_eq mem_tlb_miss pmf_m surjective_pairing t1)
                  have sum1: "folds (\<lambda>t p. snd t + p) 0 {t. \<exists>m \<in> mem_req tlb_comp. t = ((fst m, fst d), snd m * snd d)} =
                              folds (\<lambda>t p. snd t * snd d + p) 0 (mem_req tlb_comp)" 
                    using folds_plus_times_input2[where ?w = "mem_req tlb_comp" and ?d = "d"]
                          mem_finite mem_nonempty mem_unique inputdist_nonempty by auto 
                  have sum2: "folds (\<lambda>t p. snd t * snd d + p) 0 (mem_req tlb_comp) = snd d * (folds (\<lambda>t p. snd t + p) 0 (mem_req tlb_comp))"
                    using folds_plus_times_input[where ?w = "mem_req tlb_comp" and ?i = "snd d"]
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
