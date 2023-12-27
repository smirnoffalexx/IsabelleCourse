section Examples

theory Stablecoin
  imports Complex_Main
begin

text \<open>Example from \<open>https://eprint.iacr.org/2021/1069.pdf\<close>.
In this work, Isabelle/HOL was used to formalize parts of stablecoin’s (Djed) informal description.
Correctness of the algorithm is guaranteed by the formal proofs of stability properties.
We consider a part of the specification as an example. 
The full formalization could be found in the paper. 
\<close>

type_synonym base_coin = real

type_synonym stable_coin = real
type_synonym reserve_coin = real
type_synonym exchange_rate = real

locale stablecoin =
  fixes r\<^sub>m\<^sub>i\<^sub>n :: real                           \<comment>\<open>minimum reserve ratio\<close>
    and r\<^sub>m\<^sub>a\<^sub>x :: real                           \<comment>\<open>maximum reserve ratio\<close>
    and fee :: real                           \<comment>\<open>commission fee\<close>
    and N\<^sub>s\<^sub>c_threshold :: stable_coin (\<open>N\<^sup>*\<^sub>s\<^sub>c\<close>)  \<comment>\<open>threshold number of stablecoins\<close>
    and p_min_rc :: base_coin (\<open>P\<^sup>m\<^sup>i\<^sup>n\<^sub>R\<^sub>C\<close>)       \<comment>\<open>parameter\<close>
  assumes r\<^sub>m\<^sub>i\<^sub>n_lower_bound: "r\<^sub>m\<^sub>i\<^sub>n > 1 + fee"
    and r\<^sub>m\<^sub>i\<^sub>n_upper_bound : "r\<^sub>m\<^sub>a\<^sub>x \<ge> r\<^sub>m\<^sub>i\<^sub>n"
    and fee_is_percentage : "fee \<in> {0 <..1 }"
  and N\<^sub>s\<^sub>c_threshold_positivity: "N\<^sup>*\<^sub>s\<^sub>c > 0"
  and p_min_rc_positivity: "P\<^sup>m\<^sup>i\<^sup>n\<^sub>R\<^sub>C > 0"

begin
abbreviation stable_coin_target_price :: "exchange_rate \<Rightarrow> base_coin" (\<open>P\<^sup>t\<^sub>S\<^sub>C[_]\<close>)
  where "P\<^sup>t\<^sub>S\<^sub>C[X] \<equiv> X"

text\<open>R - current reserve (state variable)
Nsc - number of stablecoins in circulation (state variable)\<close>
definition stable_coin_actual_price :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> base_coin" ("P\<^sub>S\<^sub>C [_, _, _]")
  where "P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C] = (if N\<^sub>S\<^sub>C = 0 then P\<^sup>t\<^sub>S\<^sub>C[X] else min P\<^sup>t\<^sub>S\<^sub>C[X] (R / N\<^sub>S\<^sub>C))"

text\<open>The portion of reserve that would need to be used to buy back all stablecoins
is known as its liabilities:\<close>
definition liabilities :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> base_coin" ("L [_,_,_]") 
  where "L [X, R, N\<^sub>S\<^sub>C] = N\<^sub>S\<^sub>C * P\<^sub>S\<^sub>C [X, R, N\<^sub>S\<^sub>C]"

definition equity :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> base_coin" ("E [_,_,_]") 
  where "E [X, R, N\<^sub>S\<^sub>C] = R - L [X, R, N\<^sub>S\<^sub>C]"

definition reserve_ratio :: "exchange_rate \<Rightarrow> base_coin \<Rightarrow> stable_coin \<Rightarrow> real" ("r [_, _, _]") 
  where "r [X, R, N\<^sub>S\<^sub>C] = R / L [X, R, N\<^sub>S\<^sub>C]"

text\<open>Nrc - number of reserve coins in circulation (state variable)\<close>
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

text\<open>Crucial property: bank never becomes insolvent, which is a condition
defined by having negative equity.\<close>

theorem no_insolvency:
  assumes "X \<ge> 0" and "R \<ge> 0" and "N\<^sub>S\<^sub>C \<ge> 0"
  shows "E[X , R, N\<^sub>S\<^sub>C] \<ge> 0"
proof -
  consider (a) "N\<^sub>S\<^sub>C = 0" | (b) "N\<^sub>S\<^sub>C \<noteq> 0" and "R / N\<^sub>S\<^sub>C \<le> P\<^sup>t\<^sub>S\<^sub>C[X]" | 
           (c) "N\<^sub>S\<^sub>C \<noteq> 0" and "R / N\<^sub>S\<^sub>C > P\<^sup>t\<^sub>S\<^sub>C[X]"
    by linarith
  then show ?thesis
  proof cases
    case a
    from `N\<^sub>S\<^sub>C = 0` have "E[X , R, N\<^sub>S\<^sub>C] = R"
      unfolding liabilities_def and equity_def by simp
    with `R \<ge> 0` show ?thesis by auto
  next
    case b
    from `N\<^sub>S\<^sub>C \<noteq> 0` and `R / N\<^sub>S\<^sub>C \<le> P\<^sup>t\<^sub>S\<^sub>C[X]` have "E[X , R, N\<^sub>S\<^sub>C] = R - N\<^sub>S\<^sub>C * (R / N\<^sub>S\<^sub>C)"
      unfolding liabilities_def and equity_def and stable_coin_actual_price_def by simp
    also from `N\<^sub>S\<^sub>C \<noteq> 0` have "... = 0" by simp
    finally show ?thesis by simp
  next
    case c
    from `N\<^sub>S\<^sub>C \<noteq> 0` have "0 = R - N\<^sub>S\<^sub>C * (R / N\<^sub>S\<^sub>C )" by simp
    also from `N\<^sub>S\<^sub>C \<ge> 0` and `N\<^sub>S\<^sub>C \<noteq> 0` and `R / N\<^sub>S\<^sub>C > P\<^sup>t\<^sub>S\<^sub>C[X]` have
      "... < R - N\<^sub>S\<^sub>C * P\<^sup>t\<^sub>S\<^sub>C[X]" by (smt mult_le_cancel_left_pos)
    also from `N\<^sub>S\<^sub>C \<noteq> 0` and `R / N\<^sub>S\<^sub>C > P\<^sup>t\<^sub>S\<^sub>C[X]` have "... = E [X, R, N\<^sub>S\<^sub>C]"
      unfolding liabilities_def and equity_def and stable_coin_actual_price_def by simp
    finally show ?thesis by simp
  qed
qed

end

end
