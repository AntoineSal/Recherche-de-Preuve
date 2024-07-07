type 'a prop =
  | Top
  | Bot
  | V of 'a
  | Not of 'a prop
  | And of 'a prop * 'a prop
  | Or of 'a prop * 'a prop
  | Impl of 'a prop * 'a prop ;;

type 'a sequent = {
  gamma : 'a prop list;
  delta : 'a prop list;
  gamma_var : 'a prop list;
  delta_var : 'a prop list; } ;;

let create_sequent l_gamma l_delta = { 
  gamma = l_gamma; 
  delta = l_delta; 
  gamma_var = []; 
  delta_var = []; } ;;

let rec member x l = List.mem x l ;;

let bot sequent = member Bot sequent.gamma || member Bot sequent.gamma_var ;;

let top sequent = member Top sequent.delta || member Top sequent.delta_var ;;

let axiom sequent = List.mem true (List.map (fun x -> member x sequent.delta ||
                                                      member x sequent.delta_var) sequent.gamma) ||  List.mem true (List.map (fun x
                                                                                                                               -> member x sequent.delta || member x sequent.delta_var) sequent.gamma_var) ;; 

exception Wrong_rule of string ;;

let and_gamma sequent = match sequent.gamma with
  | And(phi, psi)::g -> {gamma = [phi]@[psi]@g; gamma_var = sequent.gamma_var;
                         delta = sequent.delta; delta_var = sequent.delta_var;} 
  | _ -> raise (Wrong_rule "And Gamma") ;;

let or_gamma sequent = match sequent.gamma with
  | Or(phi, psi)::g -> 
      ({gamma = [phi]@g; gamma_var = sequent.gamma_var; delta = sequent.delta;
        delta_var = sequent.delta_var;}, 
       {gamma = [psi]@g; gamma_var = sequent.gamma_var; delta = sequent.delta;
        delta_var = sequent.delta_var;}) 
  | _ -> raise (Wrong_rule "Or Gamma") ;;

let impl_gamma sequent = match sequent.gamma with
  | Impl(phi, psi)::g -> 
      ({gamma = g; gamma_var = sequent.gamma_var; delta = [phi]@sequent.delta;
        delta_var = sequent.delta_var;}, 
       {gamma = [psi]@g; gamma_var = sequent.gamma_var; delta = sequent.delta;
        delta_var = sequent.delta_var;}) 
  | _ -> raise (Wrong_rule "Impl Gamma") ;;

let not_gamma sequent = match sequent.gamma with
  | Not(phi)::g -> {gamma = g; gamma_var = sequent.gamma_var; delta =
                                                                [phi]@sequent.delta; delta_var = sequent.delta_var;} 
  | _ -> raise (Wrong_rule "Not Gamma") ;;

let and_delta sequent = match sequent.delta with
  | And(phi, psi)::d -> 
      ({gamma = sequent.gamma; gamma_var = sequent.gamma_var; delta = [phi]@d;
        delta_var = sequent.delta_var;},
       {gamma = sequent.gamma; gamma_var = sequent.gamma_var; delta = [psi]@d;
        delta_var = sequent.delta_var;})
  | _ -> raise (Wrong_rule "And Delta") ;;

let or_delta sequent = match sequent.delta with
  | Or(phi, psi)::d -> {gamma = sequent.gamma; gamma_var = sequent.gamma_var;
                        delta = [phi]@[psi]@d; delta_var = sequent.delta_var;}
  | _ -> raise (Wrong_rule "Or Delta") ;;

let impl_delta sequent = match sequent.delta with
  | Impl(phi, psi)::d -> {gamma = [phi]@sequent.gamma; gamma_var =
                                                         sequent.gamma_var; delta = [psi]@d; delta_var = sequent.delta_var;} 
  | _ -> raise (Wrong_rule "Impl Delta") ;;

let not_delta sequent = match sequent.delta with
  | Not(phi)::d -> {gamma = [phi]@sequent.gamma; gamma_var = sequent.gamma_var;
                    delta = d; delta_var = sequent.delta_var;} 
  | _ -> raise (Wrong_rule "Not Delta") ;;

let rec simplifier_gamma sequent = match sequent.gamma with
  | [] -> {gamma = []; gamma_var = sequent.gamma_var; delta = sequent.delta;
           delta_var = sequent.delta_var}
  | Top::g -> {gamma = g; gamma_var = [Top]@sequent.gamma_var; delta =
                                                                 sequent.delta; delta_var = sequent.delta_var}
  | Bot::g -> {gamma = g; gamma_var = [Bot]@sequent.gamma_var; delta =
                                                                 sequent.delta; delta_var = sequent.delta_var}
  | V(x)::g -> {gamma = g; gamma_var = [V(x)]@sequent.gamma_var; delta =
                                                                   sequent.delta; delta_var = sequent.delta_var}
  | Not(phi)::g -> not_gamma sequent
  | And(phi, psi)::g -> and_gamma sequent
  | Or(phi, psi)::g -> or_gamma sequent
  | Impl(phi, psi)::g -> impl_gamma sequent 
  | _ -> failwith "Impossible" ;;

let rec simplifier_delta sequent = match sequent.delta with
  | [] -> {gamma = sequent.gamma; gamma_var = sequent.gamma_var; delta = [];
           delta_var = sequent.delta_var}
  | Top::d -> {gamma = sequent.gamma; gamma_var = [Top]@sequent.gamma_var; delta
                                                                           = d; delta_var = [Top]@sequent.delta_var}
  | Bot::d -> {gamma = sequent.gamma; gamma_var = [Bot]@sequent.gamma_var; delta
                                                                           = d; delta_var = [Bot]@sequent.delta_var}
  | V(x)::d -> {gamma = sequent.gamma; gamma_var = [V(x)]@sequent.gamma_var;
                delta = d; delta_var = [V(x)]@sequent.delta_var}
  | Not(phi)::d -> not_delta sequent
  | And(phi, psi)::d -> and_delta sequent
  | Or(phi, psi)::d -> or_delta sequent
  | Impl(phi, psi)::d -> impl_delta sequent 
  | _ -> failwith "Impossible" ;;

let rec proof_search sequent = match sequent.gamma, sequent.delta with
  | [], [] -> bot sequent || top sequent || axiom sequent 
  | g, d -> proof_search (simplifier_gamma sequent)
  | [], d -> proof_search (simplifier_delta sequent) 
  | _ -> failwith "Impossible";;