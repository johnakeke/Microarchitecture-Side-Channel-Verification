theory Cache_Security
imports Cache_Model
begin

subsection{*Top layer state machine*}

datatype Process_Config = ProConf process_id process_name
type_synonym process = "process_id \<rightharpoonup> Process_Config"

record Sys_Config = processconf :: process

primrec get_processid :: "Process_Config \<Rightarrow> process_id"
  where "get_processid (ProConf pid _) = pid"

primrec get_processname :: "Process_Config \<Rightarrow> process_name"
  where "get_processname (ProConf _ pname) = pname"

definition is_a_process :: "Sys_Config \<Rightarrow> process_id \<Rightarrow> bool"
  where "is_a_process sc pid \<equiv> (processconf sc) pid \<noteq> None"

definition get_proconf_byid :: "Sys_Config \<Rightarrow> process_id \<Rightarrow> Process_Config option"
  where "get_proconf_byid sc pid \<equiv> (processconf sc) pid"

definition sys_config_witness :: Sys_Config
  where "sys_config_witness \<equiv> \<lparr>processconf = Map.empty\<rparr>"

consts sysconf :: "Sys_Config"
specification(sysconf)
  process_id_conf: "\<forall>p. get_proconf_byid sysconf p \<noteq> None
                        \<longrightarrow> get_processid (the (get_proconf_byid sysconf p)) = p"
  process_diff: "\<forall>P1 P2. P1 \<noteq> P2 \<longrightarrow> get_processid P1 \<noteq> get_processid P2"
  using sys_config_witness_def get_proconf_byid_def
  sorry

record State = current :: process_id
               content :: cache
               mapping :: index_mapping


definition Access :: "Sys_Config \<Rightarrow> State \<Rightarrow> ca_index \<Rightarrow> ca_tag \<Rightarrow> State"
  where "Access sc s ci ct \<equiv>
          if get_proconf_byid sc (current s) \<noteq> None then
            let r = access_line (current s) ci ct (mapping s) (content s) in
            s\<lparr>content := r\<rparr>
          else s"

definition Evict :: "Sys_Config \<Rightarrow> State \<Rightarrow> ca_index \<Rightarrow> ca_tag \<Rightarrow> State"
  where "Evict sc s ci ct \<equiv>
          if get_proconf_byid sc (current s) \<noteq> None then
            let r = evict_line (current s) ci ct (mapping s) (content s) in
            s\<lparr>content := r\<rparr>
          else s"

definition state_witness :: State
  where "state_witness \<equiv> \<lparr>current = (SOME x. (processconf sysconf) x \<noteq> None),
                          content = {},
                          mapping = (\<lambda> p. (case ((processconf sysconf) p) of None \<Rightarrow> None
                                                                           | Some (ProConf _ _) \<Rightarrow> Some {}))\<rparr>"

consts s0 :: State
specification(s0)
  s0_init: "s0 = state_witness"
  "\<forall>p. (processconf sysconf) p \<noteq> None \<longrightarrow> (the (mapping s0 p)) \<noteq> {}"
  "\<forall>p1 p2. p1 \<noteq> p2 \<and>
      (processconf sysconf) p1 \<noteq> None \<and>
      (processconf sysconf) p2 \<noteq> None \<longrightarrow>
      (the (mapping s0 p1)) \<inter> (the (mapping s0 p2)) = {}"
  sorry

datatype Hypercall = ACCESS ca_index ca_tag |
                     EVICT ca_index ca_tag
datatype Syscall = SCHEDULE
datatype Event = hyp Hypercall | sys Syscall

primrec event_enabled :: "State \<Rightarrow> Event \<Rightarrow> bool"
  where "event_enabled s (hyp h) = (is_a_process sysconf (current s))" |
        "event_enabled s (sys h) = (case h of SCHEDULE \<Rightarrow> True)" 

definition exec_event :: "Event \<Rightarrow> (State \<times> State) set"
  where "exec_event e = {(s, s'). s' \<in> (if event_enabled s e then
                                           (case e of hyp (ACCESS ci ct) \<Rightarrow> {(Access sysconf s ci ct)} |
                                                      hyp (EVICT ci ct) \<Rightarrow> {(Evict sysconf s ci ct)} |
                                                      sys SCHEDULE \<Rightarrow> Schedule sysconf s)
                                        else {s})}"

definition process_mem :: "process_id \<Rightarrow> cache \<Rightarrow> cache"
  where "process_mem pid B \<equiv> {l. l \<in> B \<and> valid l = VALID \<and> pid \<in> the (owner l)}"

primrec process_of_event :: "State \<Rightarrow> Event \<Rightarrow> process_id option"
where "process_of_event s (hyp h) = Some (current s)" |
      "process_of_event s (sys h) = Some (scheduler sysconf)"

definition interference1 :: "process_id \<Rightarrow> process_id \<Rightarrow> bool" ("(_ \<leadsto> _)")
  where "interference1 d1 d2 \<equiv>
            if d1 = d2 then True
            else if is_a_scheduler sysconf d1 then True
            else False"

definition non_interference1 :: "process_id \<Rightarrow> process_id \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)")
      where "(u \<setminus>\<leadsto>  v) \<equiv> \<not> (u \<leadsto> v)"

declare non_interference1_def [cong] and interference1_def [cong] and process_of_event_def[cong] and
       event_enabled_def[cong] and is_a_process_def[cong] and is_a_scheduler_def[cong]

lemma nintf_neq: "u \<setminus>\<leadsto>  v \<Longrightarrow> u \<noteq> v"  by auto

lemma nintf_reflx: "interference1 u u" by auto

definition vpeq_process :: "State \<Rightarrow> process_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_process s d t \<equiv> process_mem d (content s) = process_mem d (content t)"

definition vpeq_schedule :: "State \<Rightarrow> process_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_schedule s d t \<equiv> current s = current t"

definition vpeq  :: "State \<Rightarrow> process_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where "vpeq s d t \<equiv>  
         (if d = scheduler sysconf then 
            (vpeq_schedule s d t)
          else if is_a_process sysconf d then 
            (vpeq_process s d t)
          else True)"

declare vpeq_process_def [cong] and vpeq_schedule_def[cong] and vpeq_def[cong] 

lemma vpeq_process_transitive_lemma : "\<forall> s t r d. vpeq_process s d t \<and> vpeq_process t d r \<longrightarrow> vpeq_process s d r"
  by auto

lemma vpeq_process_symmetric_lemma:"\<forall> s t d. vpeq_process s d t \<longrightarrow> vpeq_process t d s"
  by auto

lemma vpeq_process_reflexive_lemma:"\<forall> s d. vpeq_process s d s"
  by auto

lemma vpeq_scheduler_transitive_lemma : "\<forall> s t r d. vpeq_schedule s d t \<and> vpeq_schedule t d r \<longrightarrow> vpeq_schedule s d r"
 by simp

lemma vpeq_scheduler_symmetric_lemma:"\<forall> s t d. vpeq_schedule s d t \<longrightarrow> vpeq_schedule t d s"
  by simp

lemma vpeq_scheduler_reflexive_lemma:"\<forall> s d. vpeq_schedule s d s"
  by simp

lemma vpeq_transitive_lemma : "\<forall> s t r d. (vpeq s d t) \<and> (vpeq t d r) \<longrightarrow> (vpeq s d r)"
  by auto

lemma vpeq_symmetric_lemma : "\<forall> s t d. (vpeq s d t) \<longrightarrow> (vpeq t d s)"
  by auto

lemma vpeq_reflexive_lemma : "\<forall> s d. (vpeq s d s)"
  by auto

lemma sched_current_lemma : "\<forall>s t a. vpeq s (scheduler sysconf) t \<longrightarrow> (process_of_event s a) = (process_of_event t a)"
  by (metis (no_types) Event.exhaust process_of_event.simps(1) process_of_event.simps(2) vpeq_def vpeq_schedule_def)
  
lemma schedeler_intf_all_help : "\<forall>d. interference1 (scheduler sysconf) d"
  by (meson interference1_def is_a_scheduler_def)

lemma no_intf_sched_help : "\<forall>d. interference1 d (scheduler sysconf) \<longrightarrow> d = (scheduler sysconf)"
  by (simp add: interference1_def is_a_scheduler_def)

lemma reachable_top: "\<forall>s a. (SM.reachable0 s0t exec_event) s \<longrightarrow> (\<exists>s'. (s, s') \<in> exec_event a)"
  proof -
  {
    fix s a
    assume p0: "(SM.reachable0 s0t exec_event) s"
    have "\<exists>s'. (s, s') \<in> exec_event a"
      proof(induct a)
        case (hyp x) show ?case 
          apply (induct x)
          by (simp add:exec_event_def)+
        next
        case (sys x) then show ?case
          apply (induct x)
          by (simp add:exec_event_def Schedule_def)+
      qed        
  }
  then show ?thesis by auto
  qed





end