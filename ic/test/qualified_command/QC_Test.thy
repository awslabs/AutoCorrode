theory QC_Test
  imports "HOL-Library.Datatype_Records"
begin

datatype_record foo =
  field_a :: nat
  field_b :: nat

context
begin

qualified datatype_record bar =
  field_x :: nat
  field_y :: nat

qualified definition get_x :: "bar \<Rightarrow> nat" where
  "get_x r \<equiv> field_x r"

end

end
