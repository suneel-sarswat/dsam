let rec comparebids (m1:Certified.fill_type list) (m2:Certified.fill_type list) ((bds:Certified.bid list)) sid = match bds with
	|[] -> (Printf.printf "\n############### Comaparison done: Everything looks all right for the stock id: %s on bids side################\n" sid)
	|b::bds' -> if (Certified.ttqb m1 b = Certified.ttqb m2 b) then comparebids m1 m2 bds' sid else 
	  (Printf.printf "\n!!!!!!!!!!!!!!!!Alert: mismatch found in stock id: %s on bid side. Please investigate further!!!!!!!!!!!!!!!!\n" sid)

let rec compareasks (m1:Certified.fill_type list) (m2:Certified.fill_type list) ((aks:Certified.ask list)) sid = match aks with
	|[] -> (Printf.printf "############### Comaparison done: Everything looks all right for the stock id: %s on asks side################\n" sid)
	|a::aks' -> if (Certified.ttqa m1 a = Certified.ttqa m2 a) then compareasks m1 m2 aks' sid else 
	  (Printf.printf "!!!!!!!!!!!!!!!!Alert: mismatch found in stock id: %s on ask side. Please investigate further!!!!!!!!!!!!!!!!\n" sid)



(*Read input data*)
let stocks = (Print.lines_from_files "stocksid")
let datadir = "exchange_inputs_outputs/"
let n = (List.length stocks)

let rec compare stocks= 
match stocks with
	|[] -> Printf.printf "\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@: All comaparisons done for the %d stocks:@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n" n
	|sid::stocks' -> 
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".bid")) 
in let bds = Print.str_list_bid_list mylist in
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".ask")) 
in let aks = Print.str_list_ask_list mylist in
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".trade")) in
let exchange_matching = Print.str_list_fill_list mylist bds aks
in comparebids (exchange_matching) (Certified.uM bds aks) bds sid; compareasks (exchange_matching) (Certified.uM bds aks) aks sid; compare stocks'

let () = compare stocks
