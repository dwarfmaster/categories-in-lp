
module type ConstrLike = sig
  type constr
  type types
  type sorts
  type univs

  val kind : Evd.evar_map -> Environ.env -> constr -> (constr,types,sorts,univs) Constr.kind_of_term
  val print : Evd.evar_map -> Environ.env -> constr -> Pp.t
  val econstr : constr -> EConstr.t
  val try_solve : Evd.evar_map -> constr -> Constr.t option
end

module CLConstr = struct
  type constr = Constr.t
  type types = Constr.t
  type sorts = Sorts.t
  type univs = Univ.Instance.t

  let kind = fun _ _ -> Constr.kind
  let print = fun sigma env -> Printer.pr_constr_env env sigma
  let econstr = EConstr.of_constr
  let try_solve = fun _ c -> Some c
end

module CLEConstr = struct
  type constr = EConstr.t
  type types = EConstr.t
  type sorts = EConstr.ESorts.t
  type univs = EConstr.EInstance.t

  let kind = fun sigma _ -> EConstr.kind sigma
  let print = fun sigma env -> Printer.pr_econstr_env env sigma
  let econstr = fun ec -> ec
  let try_solve = EConstr.to_constr_opt
end
