let stocks = (Print.lines_from_files "stocksid")
let datadir = "exchange_inputs_outputs/"
let certdatadir = "certified_outputs/"
let rec create_trades stocks= 
match stocks with
	|[] -> ()
	|sid::stocks' -> 
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".bid")) 
in let bds = Print.str_list_bid_list mylist in
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".ask")) 
in let aks = Print.str_list_ask_list mylist
in let m = (Certified.uM bds aks)
in Print.writematching (certdatadir ^ sid ^ ".trade") m;Print.printm m sid; create_trades stocks'

let () = create_trades stocks
