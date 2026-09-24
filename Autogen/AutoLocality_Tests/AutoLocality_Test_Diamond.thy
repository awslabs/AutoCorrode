(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Diamond
  imports AutoLocality_Test_Diamond_Left AutoLocality_Test_Diamond_Right
begin
(*>*)

section\<open>Import-diamond merge behavior\<close>

lemma \<open>diamond_base_attr (diamond_left_op (diamond_base_op R)) =
    diamond_base_attr R\<close>
  by simp

lemma \<open>diamond_left_attr (diamond_right_op (diamond_left_op R)) =
    diamond_left_attr R\<close>
  by simp

lemma \<open>diamond_right_attr (diamond_base_op (diamond_right_op R)) =
    diamond_right_attr R\<close>
  by simp

ML\<open>
  val ctxt = \<^context>
  val rec_name = "AutoLocality_Test_Diamond_Base.diamond_rec"
  val entries = get_record_locality_entries rec_name ctxt
  fun entries_for const_name =
    entries |> filter (fn entry => #const_name entry = const_name)
  val base_ops =
    entries_for "AutoLocality_Test_Diamond_Base.diamond_base_op"
  val base_attrs =
    entries_for "AutoLocality_Test_Diamond_Base.diamond_base_attr"
  val registered_attributes = get_attributes ctxt
  val registered_dispatch_keys =
    registered_attributes
    |> map (locality_dispatch_key_of_entry ctxt o #2)
    |> distinct locality_dispatch_key_eq
  val inventory =
    LocalityDispatcherInventory.get (Context.Proof ctxt)
  val installed_locality_dispatchers =
    Raw_Simplifier.simpset_of ctxt
    |> Raw_Simplifier.dest_ss
    |> #simprocs
    |> filter
         (String.isSubstring "_locality_dispatch_"
           o Long_Name.base_name o fst)
  val base_dispatchers =
    (case base_attrs of
       [entry] =>
         let
           val dispatch_key =
             locality_dispatch_key_of_entry ctxt entry
           val expected =
             (case LocalityDispatchKeyTable.lookup
                     inventory dispatch_key of
                SOME entry => #source_name entry
              | _ => "")
         in
           installed_locality_dispatchers
           |> filter (fn (name, _) => name = expected)
         end
     | _ => [])
  val base_inventory_entries =
    (case base_attrs of
       [entry] =>
         let
           val dispatch_key =
             locality_dispatch_key_of_entry ctxt entry
         in
           LocalityDispatchKeyTable.dest inventory
           |> filter (fn (key, _) =>
                locality_dispatch_key_eq (key, dispatch_key))
         end
     | _ => [])
  val _ = AutoLocality_Assert.run_suite "Diamond/merge"
    [ ("common operation is merged into one complete entry",
         fn () => AutoLocality_Assert.check "one common operation"
           (case base_ops of
              [entry] =>
                not (null (#core_thms entry)) andalso
                not (null (#disjoint_thms entry)) andalso
                Option.isSome (#local_thm entry)
            | _ => false)),
      ("common attribute is merged into one complete entry",
         fn () => AutoLocality_Assert.check "one common attribute"
           (case base_attrs of
              [entry] =>
                not (null (#core_thms entry))
            | _ => false)),
      ("both branch-local operation registrations survive",
         fn () => AutoLocality_Assert.check "branch operations"
           (length (entries_for
              "AutoLocality_Test_Diamond_Left.diamond_left_op") = 1 andalso
            length (entries_for
              "AutoLocality_Test_Diamond_Right.diamond_right_op") = 1)),
      ("diamond imports install one raw dispatcher per attribute family",
         fn () => AutoLocality_Assert.check "stable family dispatcher identity"
           (length installed_locality_dispatchers =
            length registered_dispatch_keys)),
      ("diamond imports retain one inventory identity per attribute family",
         fn () => AutoLocality_Assert.check "stable family inventory identity"
           (LocalityDispatchKeyTable.size inventory =
            length registered_dispatch_keys)),
      ("common-origin base family has one inventory identity",
         fn () => AutoLocality_Assert.check "one common inventory identity"
           (case base_inventory_entries of
              [(_, entry : locality_dispatcher_inventory_entry)] =>
                #1 (Simplifier.check_simproc
                  ctxt (#alias entry, Position.none)) =
                    #alias entry
            | _ => false)),
      ("common-origin base family has one raw dispatcher",
         fn () => AutoLocality_Assert.check "one common raw dispatcher"
           (length base_dispatchers = 1)) ]
\<close>

(*<*)
end
(*>*)
