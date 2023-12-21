theory Stablecoin
  imports Complex_Main
begin

type_synonym base_coin = real

type_synonym stable_coin = real
type_synonym reserve_coin = real
type_synonym exchange_rate = real

locale stablecoin =
  fixes r\<^sub>m\<^sub>i\<^sub>n :: real
    and r\<^sub>m\<^sub>a\<^sub>x :: real
    and fee :: real
    and N\<^sub>s\<^sub>c_threshold :: stable_coin (\<open>N\<^sup>*\<^sub>s\<^sub>c\<close>)
    and p_min_rc :: base_coin (\<open>P\<^sup>m\<^sup>i\<^sup>n\<^sub>R\<^sub>C\<close>)
  assumes r\<^sub>m\<^sub>i\<^sub>n_lower_bound: "r\<^sub>m\<^sub>i\<^sub>n > 1 + fee"
    and r\<^sub>m\<^sub>i\<^sub>n_upper_bound : "r\<^sub>m\<^sub>a\<^sub>x \<ge> r\<^sub>m\<^sub>i\<^sub>n"
    and fee_is_percentage : "fee \<in> {0 <..1 }"
  and N\<^sub>s\<^sub>c_threshold_positivity: "N\<^sup>*\<^sub>s\<^sub>c > 0"
  and p_min_rc_positivity: "P\<^sup>m\<^sup>i\<^sup>n\<^sub>R\<^sub>C > 0"

begin
abbreviation stable_coin_target_price :: "exchange_rate \<Rightarrow> base_coin" (\<open>P\<^sup>t\<^sub>S\<^sub>C[_]\<close>)
  where "P\<^sup>t\<^sub>S\<^sub>C[X] \<equiv> X"

definition stable_coin_actual_price :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> base_coin" ("P\<^sub>S\<^sub>C [_, _, _]")
  where "P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C] = (if N\<^sub>S\<^sub>C = 0 then P\<^sup>t\<^sub>S\<^sub>C[X] else min P\<^sup>t\<^sub>S\<^sub>C[X] (R / N\<^sub>S\<^sub>C))"

definition liabilities :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> base_coin" ("L [_,_,_]") 
  where "L [X, R, N\<^sub>S\<^sub>C] =N\<^sub>S\<^sub>C * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C]"

definition equity :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> base_coin" ("E [_,_,_]") 
  where "E [X, R, N\<^sub>S\<^sub>C] = R - L [X, R, N\<^sub>S\<^sub>C]"

definition reserve_ratio :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> real" ("r [_, _, _]") 
  where "r [X, R, N\<^sub>S\<^sub>C] = R / L [X, R, N\<^sub>S\<^sub>C]"

definition reserve_coin_target_price :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> reserve_coin \<Rightarrow> base_coin" 
  ("P\<^sup>t\<^sub>R\<^sub>C [_, _, _, _]") where
  "P\<^sup>t\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C] = E [X, R, N\<^sub>S\<^sub>C] / N\<^sub>R\<^sub>C"

definition reserve_coin_buying_price :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> reserve_coin \<Rightarrow> base_coin" 
  ("P\<^sup>b\<^sub>R\<^sub>C [_, _, _, _]") where
  "P\<^sup>b\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C] = (if N\<^sub>R\<^sub>C = 0 then P\<^sup>m\<^sup>i\<^sup>n\<^sub>R\<^sub>C else max P\<^sup>t\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C] P\<^sup>m\<^sup>i\<^sup>n\<^sub>R\<^sub>C)"

type_synonym bank_state = "base_coin \<times> stable_coin \<times> reserve_coin"

fun is_valid_bank_state :: "bank_state \<Rightarrow> bool" where
  "is_valid_bank_state (R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = (R \<ge> 0 \<and> N\<^sub>S\<^sub>C \<ge> 0 \<and> N\<^sub>R\<^sub>C \<ge> 0 )"

datatype action = BuySCs stable_coin | SellSCs stable_coin | BuyRCs reserve_coin | SellRCs reserve_coin
type_synonym transaction = "action \<times> exchange_rate"

fun tx_rate :: "transaction \<Rightarrow> exchange_rate" where
"tx_rate (_, X ) = X"

fun is_valid_transaction :: "transaction \<Rightarrow> bank_state \<Rightarrow> bool" where
"is_valid_transaction (BuySCs n, X) (R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = (X > 0 \<and> n > 0 \<and>
r [X , R, N\<^sub>S\<^sub>C] \<ge> r\<^sub>m\<^sub>i\<^sub>n \<and> r[X , R + n * (1 + fee) * P\<^sub>S\<^sub>C[X , R, N\<^sub>S\<^sub>C], N\<^sub>S\<^sub>C
+ n] \<ge> r\<^sub>m\<^sub>i\<^sub>n)" | 
"is_valid_transaction (SellSCs n, X) (R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = (X > 0 \<and> n > 0 \<and>
n * (1 - fee) * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C] \<le> R \<and> n \<le> N\<^sub>S\<^sub>C)"
| "is_valid_transaction (BuyRCs n, X) (R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = (X > 0 \<and> n > 0
\<and> (r [X , R, N\<^sub>S\<^sub>C] \<le> r\<^sub>m\<^sub>a\<^sub>x \<or> N\<^sub>S\<^sub>C < N\<^sup>*\<^sub>s\<^sub>c) \<and> r[X , R + n * (1 + fee) * P\<^sup>b\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C], N\<^sub>S\<^sub>C] \<le> r\<^sub>m\<^sub>a\<^sub>x)"
| "is_valid_transaction (SellRCs n, X) (R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = (X > 0 \<and> n > 0 \<and> n
* (1 - fee) * P\<^sup>t\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C] \<le> R \<and> n \<le> N\<^sub>R\<^sub>C \<and> r [X , R, N\<^sub>S\<^sub>C] \<ge>
r\<^sub>m\<^sub>i\<^sub>n \<and> r [X , R - n * (1 - fee) * P\<^sup>t\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C], N\<^sub>S\<^sub>C] \<ge> r\<^sub>m\<^sub>i\<^sub>n)"

inductive transition :: "bank_state \<Rightarrow> transaction \<Rightarrow> bank_state \<Rightarrow> bool" ("_\<rightarrow>\<lbrace>_\<rbrace> _" [51 , 0 , 51 ] 50) 
  where
buy_scs: "S \<rightarrow>\<lbrace>tx\<rbrace> S'"
  if "is_valid_transaction tx S"
    and "is_valid_bank_state S"
    and "(BuySCs n, X) = tx"
    and "(R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = S"
    and "R' = R + n * (1 + fee) * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C]"
    and "N\<^sub>S\<^sub>C' = N\<^sub>S\<^sub>C + n"
    and "N\<^sub>R\<^sub>C' = N\<^sub>R\<^sub>C"
    and "S' = (R', N\<^sub>S\<^sub>C', N\<^sub>R\<^sub>C')"
| sell_scs: "S \<rightarrow>\<lbrace>tx\<rbrace> S'"
  if "is_valid_transaction tx S"
    and "is_valid_bank_state S"
    and "(SellSCs n, X) = tx"
    and "(R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = S"
    and "R' = R - n * (1 - fee) * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C]"
    and "N\<^sub>S\<^sub>C' = N\<^sub>S\<^sub>C - n"
    and "N\<^sub>R\<^sub>C' = N\<^sub>R\<^sub>C"
    and "S' = (R', N\<^sub>S\<^sub>C', N\<^sub>R\<^sub>C')"
| buy_rcs: "S \<rightarrow>\<lbrace>tx\<rbrace> S'"
  if "is_valid_transaction tx S"
  and "is_valid_bank_state S"
  and "(BuyRCs n, X ) = tx"
  and "(R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = S"
  and "R' = R + n * (1 + fee) * P\<^sup>b\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C]"
  and "N\<^sub>S\<^sub>C' = N\<^sub>S\<^sub>C"
  and "N\<^sub>R\<^sub>C' = N\<^sub>R\<^sub>C + n"
  and "S' = (R', N\<^sub>S\<^sub>C', N\<^sub>R\<^sub>C')"
| sell_rcs: "S \<rightarrow>\<lbrace>tx\<rbrace> S'"
  if "is_valid_transaction tx S"
    and "is_valid_bank_state S"
    and "(SellRCs n, X ) = tx"
    and "(R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = S"
    and "R' = R - n * (1 - fee) * P\<^sup>t\<^sub>R\<^sub>C [X, R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C]"
    and "N\<^sub>S\<^sub>C' = N\<^sub>S\<^sub>C"
    and "N\<^sub>R\<^sub>C' = N\<^sub>R\<^sub>C - n"
    and "S' = (R', N\<^sub>S\<^sub>C', N\<^sub>R\<^sub>C')"

inductive sequence_transition :: "bank_state \<Rightarrow> transaction list \<Rightarrow> bank_state \<Rightarrow> bool" 
("_ \<rightarrow>\<^sup>*\<lbrace>_\<rbrace> _" [51 , 0 , 51 ] 50) where
tx_seq_base: "S \<rightarrow>\<^sup>*\<lbrace>[]\<rbrace> S"  | 
txs_seq_ind: "S \<rightarrow>\<^sup>*\<lbrace>txs @ [tx]\<rbrace> S"
  if "S \<rightarrow>\<^sup>*\<lbrace>txs\<rbrace> S''"
    and "S''\<rightarrow>\<lbrace>tx\<rbrace> S'"
    and "S'' = (R'', N\<^sub>S\<^sub>C'', N\<^sub>R\<^sub>C'')"
    and "N\<^sub>S\<^sub>C'' > 0"
    and "N\<^sub>R\<^sub>C'' > 0"

datatype market_offer = BuySCOffer | SellSCOffer

type_synonym secondary_market = "market_offer \<times> base_coin"

datatype market_choice = Bank | Secondary

fun one_sc_transaction :: "exchange_rate \<Rightarrow> market_offer \<Rightarrow> transaction" where
  "one_sc_transaction X SellSCOffer = (BuySCs 1 , X )" (* a ‘Buy 1 SC’ transaction *)
| "one_sc_transaction X BuySCOffer = (SellSCs 1 , X )" (* a ‘Sell 1 SC’ transaction *)


fun rational_choice :: "bank_state \<Rightarrow> exchange_rate \<Rightarrow> secondary_market \<Rightarrow> market_choice" where
"rational_choice S X (action, price) = (
  let
    (R, N\<^sub>S\<^sub>C, N\<^sub>R\<^sub>C) = S;
    tx = one_sc_transaction X action
  in 
    if \<not> (is_valid_bank_state S \<and> is_valid_transaction tx S)
    then
      Secondary 
    else
      case action of
      SellSCOffer \<Rightarrow> (if price > (1 + fee) * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C] then Bank
      else Secondary)
      | BuySCOffer \<Rightarrow> (if price < (1 - fee) * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C] then Bank
      else Secondary))"

theorem peg_maintenance_upper_bound:
  assumes "action = SellSCOffer"
    and "tx = one_sc_transaction X action" (* a ‘Buy 1 SC’ transaction *)
    and "S \<rightarrow>\<lbrace>tx\<rbrace> S'" (* the transaction is allowed *)
    and "secondary_market = (action, price)"
    and "price > (1 + fee) * P\<^sup>t\<^sub>S\<^sub>C[X]"
  shows "\<not> rational_choice S X secondary_market = Secondary"
proof -
  obtain R and N\<^sub>S\<^sub>C and N\<^sub>R\<^sub>C where f: "(R, N\<^sub>S\<^sub>C , N\<^sub>R\<^sub>C) = S"
    by (metis (no_types) is_valid_bank_state.cases)
  let ?P' = "(1 + fee) * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C]"
  have "?P' \<le> (1 + fee) * P\<^sup>t\<^sub>S\<^sub>C[X]"
    unfolding stable_coin_actual_price_def using fee_is_percentage by auto
  with assms(5) have "?P' < price"
    by linarith
  moreover from assms(3) have "is_valid_bank_state S" and "is_valid_transaction tx S"
    by (blast intro: transition.cases)+
  ultimately have "rational_choice S X secondary_market = Bank"
    using assms(1, 2, 4) and f 
    by (simp split: prod.splits) blast
  then show ?thesis
    by simp
qed

end

end
