  type ide = string;;

  type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
    Eq of exp * exp | Negative of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
    Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp list |
    Letrec of ide * exp * exp
    | Dictionary of (ide * exp) list (*Dizionario*)
    | FunBin of ide * ide * exp (*Funzioni Binarie*)
    | Insert of ide * exp * exp (*Funzione insert*)
    | Delete of ide * exp (*Funzione delete*)
    | HasKey of ide * exp (*Funzione has_key*)
    | Iterate of exp * exp (*Funzione iterate*)
    | Filter of ide list * exp (*Funzione filter*)
    | Fold of exp * exp (*Funzione fold*)

  type 't env = ide -> 't;;
  let emptyenv (v : 't) = function x -> v;;
  let applyenv (r : 't env) (i : ide) = r i;;
  let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

  type evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun
              | DictVal of (ide * evT) list (*Dizionario esprimibile*)
              | FunBinVal of evFunBin (*Funzioni binarie esprimibili*)
  and evFun = ide * exp * evT env
  and evFunBin = ide * ide * exp * evT env;;

  let typecheck (s : string) (v : evT) : bool =
    match s with
    | "int" -> (match v with
                | Int(_) -> true
                | _ -> false
    )
    | "bool" -> (match v with
                | Bool(_) -> true
                | _ -> false
    )
    | _ -> failwith("not a valid type");;

  let prod x y =
    if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
          | (Int(n),Int(u)) -> Int(n*u)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let sum x y =
    if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
          | (Int(n),Int(u)) -> Int(n+u)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let diff x y =
    if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
          | (Int(n),Int(u)) -> Int(n-u)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let eq x y =
    if (typecheck "int" x) && (typecheck "int" y)
    then (match (x,y) with
          | (Int(n),Int(u)) -> Bool(n=u)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let negative x =
    if (typecheck "int" x)
    then (match x with
          | Int(n) -> Int(-n)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let iszero x =
    if (typecheck "int" x)
    then (match x with
          | Int(n) -> Bool(n=0)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let orExp x y =
    if (typecheck "bool" x) && (typecheck "bool" y)
    then (match (x,y) with
          | (Bool(b),Bool(e)) -> (Bool(b||e))
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let andExp x y =
    if (typecheck "bool" x) && (typecheck "bool" y)
    then (match (x,y) with
          | (Bool(b),Bool(e)) -> Bool(b&&e)
          | _ -> failwith("error in applying function"))
    else failwith("Type error");;

  let non x =
    if (typecheck "bool" x)
    then (match x with
          | Bool(true) -> Bool(false)
          | Bool(false) -> Bool(true)
          | _ -> failwith("Type error")
    )
    else failwith("Type error");;

  let rec eval (e : exp) (r : evT env) : evT = match e with
        Eint n -> Int n 
      | Ebool b -> Bool b
      | IsZero a -> iszero (eval a r) 
      | Den i -> applyenv r i 
      | Eq(a, b) -> eq (eval a r) (eval b r) 
      | Prod(a, b) -> prod (eval a r) (eval b r) 
      | Sum(a, b) -> sum (eval a r) (eval b r) 
      | Diff(a, b) -> diff (eval a r) (eval b r) 
      | Negative a -> negative (eval a r)
      | And(a, b) -> andExp (eval a r) (eval b r)
      | Or(a, b) -> orExp (eval a r) (eval b r) 
      | Not a -> non (eval a r) 
      | Ifthenelse(a, b, c) -> let g = (eval a r) in
                                if (typecheck "bool" g) then (if g = Bool(true) then (eval b r) else (eval c r))
                                else failwith ("nonboolean guard")
      | Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
      | Fun(i, a) -> FunVal(i, a, r)
      | FunBin(i1, i2, a) -> FunBinVal(i1, i2, a, r) (*Funzioni binarie*)
      | FunCall(f, eArg) -> let fClosure = (eval f r) in (*
                                                            Gestisco gli eArg come una lista di argomenti ed aggiungo il match per FunBinVal
                                                            dove faccio il bind dei primi due elementi della lista di argomenti ad arg1 e arg2
                                                          *)
                                (match fClosure with
                                    FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval (List.nth eArg 0) r))
                                  | FunBinVal(arg1, arg2, fBody, fDecEnv) -> eval fBody ( bind (bind fDecEnv arg2 (eval (List.nth eArg 1) r))
                                                                                              arg1 (eval (List.nth eArg 0) r)
                                                                                        )
                                  | RecFunVal(g, (arg, fBody, fDecEnv)) -> let aVal = (eval (List.nth eArg 0) r) in
                                                                        let rEnv = (bind fDecEnv g fClosure) in
                                                                          let aEnv = (bind rEnv arg aVal) in
                                                                            eval fBody aEnv
                                  | _ -> failwith("non functional value")) 
      | Letrec(f, funDef, letBody) ->  (match funDef with
                                          Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                                                eval letBody r1 
                                          |_ -> failwith("non functional def"))
      | Dictionary(lista) -> let rec eval_lista evT_lista = match evT_lista with (*Dizionario*)
                                [] -> []
                                | (id,h) :: t -> (id, eval h r) :: (eval_lista t)
                              in DictVal(eval_lista lista)
      | Insert(id, valore, dict) -> ( let rec insert id valore dict = match dict with (*Funzione insert*)
                                                [] -> [(id, eval valore r)]
                                                | (id_h, val_h)::t -> if (id_h=id) then failwith("Key already exists!") else (id_h, val_h)::(insert id valore t)
                                    in match eval dict r with
                                      | DictVal(lista) -> DictVal(insert id valore lista)
                                      | _ -> failwith("Not a dictionary!")
      )
      | Delete(id, dict) -> (let rec del id dict = match dict with (*Funzione delete*)
                                            [] -> failwith("Key not found!")
                                            | (id_h, val_h)::t -> if (id_h=id) then t else (id_h, val_h)::(del id t)
                            in match eval dict r with
                                | DictVal(lista) -> DictVal(del id lista)
                                | _ -> failwith("Not a dictionary!")
      )
      | HasKey(id, dict) -> (let rec has_key id dict = match dict with  (*Funzione has_key*)
                                                [] -> Bool(false)
                                                | (id_h, _)::t -> if (id_h=id) then Bool(true) else has_key id t
                            in match eval dict r with
                                | DictVal(lista) -> has_key id lista
                                | _ -> failwith("Not a dictionary!")
      )
      | Iterate(f, dict) -> (let rec apply f dict = match dict with (*Funzione iterate, valida solo per interi e booleani, in quanto ha poco senso con gli altri tipi esprimibili*)
                                [] -> []
                              | (id_h, val_h)::t -> match val_h with 
                                                      Int(act_val) -> (id_h, eval (FunCall(f,[Eint(act_val)])) r):: apply f t
                                                    |  Bool(act_val) -> (id_h, eval (FunCall(f,[Ebool(act_val)])) r):: apply f t
                                                    | _ -> failwith("Type error!")
                            in match eval dict r with
                              | DictVal(lista) -> DictVal(apply f lista)
                              | _ -> failwith("Not a dictionary!")
      )
      | Filter(id_list, dict) -> (let rec filter id dict = match dict with (*Funzione filter*)
                                        [] -> []
                                        | (id_h, val_h)::t -> if (List.mem id_h id) then (id_h, val_h)::(filter id t) else filter id t
                                  in match eval dict r with
                                  | DictVal(lista) -> DictVal(filter id_list lista)
                                  | _ -> failwith("Not a dictionary!")

      )
      | Fold(f, dict) -> ( (*Funzione fold, valida solo per interi, necessita di una f che sia una funzione binaria FunBin, valida solo per gli interi*)
            let rec fold f acc dict = match dict with 
              [] -> acc
              | (_, val_h)::t -> match (acc, val_h) with
                  Int(acc_evT), Int(val_evT) -> fold f (eval (FunCall(f, [Eint(acc_evT); Eint(val_evT)])) r) t
                  | _,_ -> failwith("Type error!")
            in match eval dict r with 
             | DictVal(lista) -> fold f (Int(0)) lista
             | _ -> failwith("Not a dictionary!")
      )
      
  ;;


  (*tests*)
  let env_test = emptyenv Unbound;;


  (*Provo due funzioni e controllo se le funzioni binarie vengono interpretate, così come le funzioni unarie *)
  let x = FunCall(FunBin("x", "y", Sum(Den "x", Den "y")), [Eint 1; Eint 2]);;
  let y = FunCall(Fun("y", Sum(Eint 1, Den "y")), [Eint 2]);;

  eval x env_test;;
  eval y env_test;;

  (*Creo un dizionario e vedo se lo interpreta*)
  let dict_test = Dictionary([("mele", Eint(430));("banane", Eint(312));("arance", Eint(525));("pere", Eint(217))]);;
  eval dict_test env_test;;

  (*Provo ad inserire un elemento non esistente, mi aspetto che non ci siano problemi*)
  let insert_test = Insert("kiwi", Eint(300), dict_test);;
  eval insert_test env_test;;

  (*Provo ad inserire un elemento esistente, mi aspetto un errore "Key already exists!"*)
  let insert2_test = Insert("mele", Eint(10), dict_test);;
  eval insert2_test env_test;;

  (*Provo ad eliminare un elemento esistente, mi aspetto che non ci siano problemi*)
  let delete_test = Delete("pere", dict_test);;
  eval delete_test env_test;;

  (*Provo ad eliminare un elemento non esistente, mi aspetto un errore "Key not found!"*)
  let delete2_test = Delete("notexists", dict_test);;
  eval delete2_test env_test;;

  (*Controllo se esiste un elemento presente, mi aspetto true*)
  let haskey_test = HasKey("banane", dict_test);;
  eval haskey_test env_test;;

  (*Controllo se esiste un elemento non presente, mi aspetto false*)
  let haskey2_test = HasKey("notexists", dict_test);;
  eval haskey2_test env_test;;

  (*Provo un iterate, mi aspetto che vada a buon fine*)
  let iterate_test = Iterate(Fun("y", Sum(Eint 1, Den "y")), dict_test);;
  eval iterate_test env_test;;

  (*Provo un iterate con un errore di tipo (usa il not su degli interi), mi aspetto un errore di tipo*)
  let iterate2_test = Iterate(Fun("y", Not(Den "y")), dict_test);;
  eval iterate2_test env_test;;

  (*Provo un filter con un elemento esistente e l'altro no, mi aspetto che vada a buon fine*)
  let filter_test = Filter(["arance";"notexists"], dict_test);;
  eval filter_test env_test;;

  (*Provo un filter con una lista vuoto, mi aspetto un dizionario vuoto*)
  let filter2_test = Filter([], dict_test);;
  eval filter2_test env_test;;

  (*Provo un fold come nell'esempio sul testo, mi aspetto che vada a buon fine*)
  let funct_test = FunBin("acc", "x", Sum(Sum(Den "x", Eint(1)), Den "acc"));;
  let fold_test = Fold(funct_test, dict_test);;
  eval fold_test env_test;;
  