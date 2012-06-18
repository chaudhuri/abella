type hhwseq = {
  ambient : Context.t ;
  context : Context.t ;
  term    : Term.term ;
}

val show_ambient : bool ref

include Spec.T with type seq = hhwseq
