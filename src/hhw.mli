type hhwseq = {
  context : Context.t ;
  term    : Term.term ;
}

include Spec.T with type seq = hhwseq
