theory Cache_Model
imports Main
begin

subsection{*Top layer: cache structure and mapping*}

typedecl process_id
typedecl process_name

typedecl tagbits
typedecl indexbits

record addr = ta :: tagbits
              ix :: indexbits

typedecl randomsalt

typedecl key

typedecl ca_index
typedecl ca_way
typedecl ca_logical

record cache_line = set :: ca_index
                    way :: ca_way
                    log :: ca_logical
                    ran :: randomsalt
                    tag :: tagbits
                    valid :: bool
                    lock :: bool
                    owner :: "process_id option"

type_synonym cache = "cache_line set"

consts C:: cache
specification(C)
  "\<forall>c1 c2. c1 \<in> C \<and> c2 \<in> C \<and> c1 \<noteq> c2 \<longrightarrow> \<not> (set c1 = set c2 \<and> way c1 = way c2)"
  by auto

type_synonym index_mapping = "indexbits \<rightharpoonup> ca_index"

definition get_index_mapping :: "indexbits \<Rightarrow> index_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line set"
  where "get_index_mapping Dib im B \<equiv> {l. l \<in> B \<and> set l = the (im Dib)}"

definition swap_index_mapping :: "indexbits \<Rightarrow> indexbits \<Rightarrow> index_mapping \<Rightarrow> index_mapping"
  where "swap_index_mapping Dib Rib im \<equiv>
          let Dci = the (im Dib);
              Rci = the (im Rib);
              im' = im(Dib := Some Rci) in
          im'(Rib := Some Dci)"

type_synonym process_mapping = "process_id \<rightharpoonup> index_mapping"

definition get_process_mapping :: "process_id \<Rightarrow> indexbits \<Rightarrow> process_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line set"
  where "get_process_mapping pid Dib pm B \<equiv> {l. l \<in> get_index_mapping Dib (the (pm pid)) B}"

definition swap_process_mapping :: "process_id \<Rightarrow> indexbits \<Rightarrow> indexbits \<Rightarrow> process_mapping \<Rightarrow> process_mapping"
  where "swap_process_mapping pid Dib Rib pm \<equiv>
          pm(pid := Some (swap_index_mapping Dib Rib (the (pm pid))))"

type_synonym logical_mapping = "indexbits \<rightharpoonup> ca_logical"

definition probe_logical_mapping :: "process_id \<Rightarrow> indexbits \<Rightarrow> logical_mapping \<Rightarrow> cache_line set \<Rightarrow> bool"
  where "probe_logical_mapping pid Dib lm B \<equiv> \<exists>!l. l \<in> B \<and> owner l = Some pid \<and> log l = the (lm Dib)"

definition get_logical_mapping :: "process_id \<Rightarrow> indexbits \<Rightarrow> logical_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line"
  where "get_logical_mapping pid Dib lm B \<equiv> THE l. l \<in> B \<and> owner l = Some pid \<and> log l = the (lm Dib)"

type_synonym random_mapping = "(process_id \<times> addr \<times> key) \<rightharpoonup> ca_index"

definition get_random_mapping :: "process_id \<Rightarrow> addr \<Rightarrow> key \<Rightarrow> random_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line set"
  where "get_random_mapping pid D k rm B \<equiv> {l. l \<in> B \<and> set l = the (rm (pid, D, k))}"

type_synonym randomsalt_mapping = "(addr \<times> randomsalt) \<rightharpoonup> ca_index"

definition get_randomsalt_mapping :: "addr \<Rightarrow> randomsalt \<Rightarrow> randomsalt_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line set"
  where "get_randomsalt_mapping D r rsm B \<equiv> {l. l \<in> B \<and> set l = the (rsm (D, r))}"

definition get_randomsalt_mapping_set :: "addr \<Rightarrow> randomsalt set \<Rightarrow> randomsalt_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line set"
  where "get_randomsalt_mapping_set D rs rsm B \<equiv> {l. \<exists> r. r \<in> rs \<and> l \<in> get_randomsalt_mapping D r rsm B}"

subsection{*Middle layer: public operations*}

definition probe_tag :: "tagbits \<Rightarrow> cache_line \<Rightarrow> bool"
  where "probe_tag tb c \<equiv> tb = tag c"

definition probe_line :: "tagbits \<Rightarrow> cache_line set \<Rightarrow> bool"
  where "probe_line tb B \<equiv> \<exists>!b. b \<in> B \<and> probe_tag tb b \<and> valid b"

definition get_line :: "tagbits \<Rightarrow> cache_line set \<Rightarrow> cache_line"
  where "get_line tb B \<equiv> THE b. b \<in> B \<and> probe_tag tb b \<and> valid b"

definition probe_line_ran :: "addr \<Rightarrow> randomsalt set \<Rightarrow> randomsalt_mapping \<Rightarrow> cache_line set \<Rightarrow> bool"
  where "probe_line_ran D rs rm B \<equiv> \<exists>!b. b \<in> B \<and> probe_tag (ta D) b \<and> valid b \<and> (\<exists> r. r \<in> rs \<and> (the (rm (D, r))) = set b)"

definition get_line_ran :: "addr \<Rightarrow> randomsalt set \<Rightarrow> randomsalt_mapping \<Rightarrow> cache_line set \<Rightarrow> cache_line"
  where "get_line_ran D rs rm B \<equiv> THE b. b \<in> B \<and> probe_tag (ta D) b \<and> valid b \<and> (\<exists> r. r \<in> rs \<and> (the (rm (D, r))) = set b)"

definition invalidate_line :: "cache_line \<Rightarrow> cache_line"
  where "invalidate_line b \<equiv> b\<lparr>valid := False, lock := False, owner := None\<rparr>"

definition invalidate_line_owner :: "process_id \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "invalidate_line_owner pid b \<equiv>
          if valid b \<and> owner b = Some pid then
            b\<lparr>valid := False, lock := False, owner := None\<rparr>
          else b"

definition invalidate_line_owner_set :: "process_id \<Rightarrow> cache_line set \<Rightarrow> cache_line set"
  where "invalidate_line_owner_set pid B = {l. \<exists> b. b \<in> B \<and> l = invalidate_line_owner pid b}"

definition update_line :: "process_id \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "update_line pid b \<equiv> b\<lparr>owner := Some pid\<rparr>"

definition update_line_lock :: "process_id \<Rightarrow> bool \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "update_line_lock pid L b \<equiv> b\<lparr>lock := L, owner := Some pid\<rparr>"

definition replace_line :: "process_id \<Rightarrow> tagbits \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "replace_line pid tb b \<equiv> b\<lparr>tag := tb, valid := True, owner := Some pid\<rparr>"

definition replace_line_lock :: "process_id \<Rightarrow> tagbits \<Rightarrow> bool \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "replace_line_lock pid tb L b \<equiv> b\<lparr>tag := tb, valid := True, lock := L, owner := Some pid\<rparr>"

definition replace_line_lock_log :: "process_id \<Rightarrow> ca_logical \<Rightarrow> tagbits \<Rightarrow> bool \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "replace_line_lock_log pid cl tb L b \<equiv> b\<lparr>log := cl, tag := tb, valid := True, lock := L, owner := Some pid\<rparr>"

definition replace_line_ran :: "process_id \<Rightarrow> tagbits \<Rightarrow> randomsalt \<Rightarrow> cache_line \<Rightarrow> cache_line"
  where "replace_line_ran pid tb r b \<equiv> b\<lparr>ran := r, tag := tb, valid := True, owner := Some pid\<rparr>"

subsection{*Third layer: specific cache models*}

definition sp_access_line :: "process_id \<Rightarrow> addr \<Rightarrow> process_mapping \<Rightarrow> cache \<Rightarrow> cache"
  where "sp_access_line pid D pm B \<equiv>
          let cls = get_process_mapping pid (ix D) pm B in
          if \<not> probe_line (ta D) cls then
            let b = SOME l. l \<in> cls;
                b' = replace_line pid (ta D) b in
            B - {b} \<union> {b'}
          else
            let m = get_line (ta D) cls;
                m' = update_line pid m in
            B - {m} \<union> {m'}"

definition sp_evict_line :: "process_id \<Rightarrow> addr \<Rightarrow> process_mapping \<Rightarrow> cache \<Rightarrow> cache"
  where "sp_evict_line pid D pm B \<equiv>
          let cls = get_process_mapping pid (ix D) pm B in
          if \<not> probe_line (ta D) cls then
            B
          else
            let b = get_line (ta D) cls;
                b' = invalidate_line b in
            B - {b} \<union> {b'}"

definition pl_access_line :: "process_id \<Rightarrow> addr \<Rightarrow> bool \<Rightarrow> index_mapping \<Rightarrow> cache \<Rightarrow> cache"
  where "pl_access_line pid D L im B \<equiv>
          let cls = get_index_mapping (ix D) im B in
          if \<not> probe_line (ta D) cls then
            let b = SOME l. l \<in> cls;
                b' = replace_line_lock pid (ta D) L b in
            if \<not> L then
              if \<not> lock b then
                B - {b} \<union> {b'}
              else
                B
            else
              if owner b = Some pid then
                B - {b} \<union> {b'}
              else
                B
          else
            let m = get_line (ta D) cls;
                m' = update_line_lock pid L m in
            B - {m} \<union> {m'}"

definition rp_access_line :: "process_id \<Rightarrow> addr \<Rightarrow> bool \<Rightarrow> process_mapping \<Rightarrow> cache \<Rightarrow> cache \<times> process_mapping"
  where "rp_access_line pid D L pm B \<equiv>
          let cls = get_process_mapping pid (ix D) pm B in
          if \<not> probe_line (ta D) cls then
            let b = SOME l. l \<in> cls in
            if owner b = Some pid then
              if lock b = L then
                let b' = replace_line_lock pid (ta D) L b in
                (B - {b} \<union> {b'}, pm)
              else
                let r = SOME l. l \<in> B;
                    r' = invalidate_line r in
                (B - {r} \<union> {r'}, pm)
            else
              let s = SOME ib. ib \<noteq> ix D;
                  cls' = get_process_mapping pid s pm B;
                  r = SOME l. l \<in> cls';
                  r' = replace_line_lock pid (ta D) L r in
              (B - {r} \<union> {r'}, swap_process_mapping pid (ix D) s pm)
          else
            let m = get_line (ta D) cls;
                m' = update_line_lock pid L m in
            (B - {m} \<union> {m'}, pm)"

definition newcache_access_line :: "process_id \<Rightarrow> addr \<Rightarrow> bool \<Rightarrow> logical_mapping \<Rightarrow> cache \<Rightarrow> cache"
  where "newcache_access_line pid D L lm B \<equiv>
          if \<not> probe_logical_mapping pid (ix D) lm B then
            let b = SOME l. l \<in> B;
                b' = replace_line_lock_log pid (the (lm (ix D))) (ta D) L b in
            B - {b} \<union> {b'}
          else
            let c = get_logical_mapping pid (ix D) lm B in
            if \<not> probe_tag (ta D) c then
              if \<not> lock c \<and> \<not> L then
                let n = replace_line pid (ta D) c in
                B - {c} \<union> {n}
              else
                let r = SOME l. l \<in> B;
                    r' = invalidate_line r in
                B - {r} \<union> {r'}
            else
              let c' = update_line_lock pid L c in
              B - {c} \<union> {c'}"

definition scatter_access_line :: "process_id \<Rightarrow> addr \<Rightarrow> key \<Rightarrow> random_mapping \<Rightarrow> cache \<Rightarrow> cache"
  where "scatter_access_line pid D k rm B \<equiv>
          let cls = get_random_mapping pid D k rm B in
          if \<not> probe_line (ta D) cls then
            let b = SOME l. l \<in> cls;
                b' = replace_line pid (ta D) b in
            B - {b} \<union> {b'}
          else
            let m = get_line (ta D) cls;
                m' = update_line pid m in
            B - {m} \<union> {m'}"

definition phantomcache_access_line :: "process_id \<Rightarrow> addr \<Rightarrow> randomsalt set \<Rightarrow> randomsalt_mapping \<Rightarrow> cache \<Rightarrow> cache"
  where "phantomcache_access_line pid D rs rsm B \<equiv>
          let cls = get_randomsalt_mapping_set D rs rsm B in
          if \<not> probe_line_ran D rs rsm cls then
            let sa = SOME r. r \<in> rs;
                cls' = get_randomsalt_mapping D sa rsm cls;
                b = SOME l. l \<in> cls';
                b' = replace_line_ran pid (ta D) sa b in
            B - {b} \<union> {b'}
          else
            let m = get_line_ran D rs rsm cls;
                m' = update_line pid m in
            B - {m} \<union> {m'}"

end
