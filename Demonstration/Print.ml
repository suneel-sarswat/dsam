open Str
(**Read data from a file**)
let read_line ic = try Some (input_line ic) with End_of_file -> None 
let lines_from_files filename = 
  let rec lines_from_files_aux ic acc = match (read_line ic) with 
    | None -> acc              (*To output in the same order, please do List.rev acc *)
    | Some s -> lines_from_files_aux ic (s :: acc) in 
  lines_from_files_aux (open_in filename) [] 

(**Functions to read bids data from the file**)
(*type bid = {idb:int;btime:int;bp:int;bq:int}*)
let createbid l:Certified.bid=
	match l with 
		|[i;t;p;q] -> {Certified.idb=i;Certified.btime=t;Certified.bp=p;Certified.bq=q}  
		|_ ->raise (Invalid_argument "Bid information is incomplete");;

let string_to_bid line=createbid (List.map int_of_string (String.split_on_char ',' line));;

(*This function takes a list of strings and converts them into list of bid records*)
let rec str_list_bid_list mylist = match mylist with
	| [] ->[]
	| line::mylist' ->(string_to_bid line)::(str_list_bid_list mylist')

(*type ask = {ida:int;stime:int;sp:int;sq:int}*)
(**Functions to read asks data from the file**)
let createask l=
	match l with 
		|[i;t;p;q] -> {Certified.ida=i;Certified.stime=t;Certified.sp=p;Certified.sq=q}  
		|_ ->raise (Invalid_argument "Ask information is incomplete");;

let string_to_ask line=createask (List.map int_of_string (String.split_on_char ',' line));;


(*This function takes a list of strings and converts them into list of ask records*)
let rec str_list_ask_list mylist = match mylist with
	| [] ->[]
	| line::mylist' ->(string_to_ask line)::(str_list_ask_list mylist')


(**Functions to read trades data from the file**)

let rec getbid (bds:Certified.bid list) i=
	match bds with 
		|[] -> Certified.b0
		|b::bds' -> if (b.idb = i) then b else getbid bds' i

let rec getask (aks:Certified.ask list) i=
	match aks with 
		|[] -> Certified.a0
		|a::aks' -> if (a.ida = i) then a else getask aks' i

let createfill l bds aks=
	match l with 
		|[i1;i2;p;q] -> {Certified.bid_of=(getbid bds i1);Certified.ask_of= (getask aks i2);Certified.tp=p;Certified.tq=q}  
		|_ ->raise (Invalid_argument "Trade information is incomplete");;

let string_to_fill line bds aks=createfill (List.map int_of_string (String.split_on_char ',' line)) bds aks;;


(*This function takes a list of strings and converts them into list of transactions*)
let rec str_list_fill_list mylist bds aks= match mylist with
	| [] ->[]
	| line::mylist' ->(string_to_fill line bds aks)::(str_list_fill_list mylist' bds aks)


(**Functions write trades data in a file**)
let rec printm (m:Certified.fill_type list) sid = match m with
	|[] -> (Printf.printf "#################### End of Trades for stock %s ####################\n\n" sid)
	|f::m' -> (Printf.printf "Buy id: %i, Sell id: %i, Price: %i, Quantity: %i\n" f.Certified.bid_of.idb f.Certified.ask_of.ida f.Certified.tp f.Certified.tq);printm m' sid


let rec printmfile oc = function 
  | [] -> ()
  | f::m -> Printf.fprintf oc "%d,%d,%d,%d\n" f.Certified.bid_of.idb f.Certified.ask_of.ida f.Certified.tp f.Certified.tq; printmfile oc m

let writematching file (m:Certified.fill_type list) =
  let oc = open_out file in
  printmfile oc m;
  close_out oc;
  
