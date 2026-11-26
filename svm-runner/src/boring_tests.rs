//! Boring, everyday exchange LiteSVM functional tests for `percolator-lean`!
//!
//! Covers all the normal, unexciting flows traders & LPs expect to "just work"
//! identically to Binance / Hyperliquid:
//!  1. Deposit / partial withdraw / re-deposit / full withdraw / close empty portfolio
//!  2. Simple bilateral Long vs Short profit & loss with trading fees & full SPL exit
//!  3. Scale-in (adding to position) & multi-step partial closes across price moves
//!  4. Position flip (Long -> flat -> Short) on the same market
//!  5. Bid/ask `execPrice` spread fills & clamp rejections
//!  6. Positive & negative funding rate accruals (Longs->Shorts and Shorts->Longs)
//!  7. Multi-trader exit order permutations (winners-first, reverse, & L->L / S->S hand-offs)
//!  8. Partial liquidation restoring health, followed by full liquidation (0 bad debt, 0 ADL)
//!  9. HLP-style liquidation takeover (`mode=1`, OI & ADL bit-for-bit invariant, Bob untouched)
//! 10. Multi-market cross-margin offsetting (BTC + ETH) & instant profit reuse without closing
//! 11. Withdrawal margin guards (`totalIm`), stale-leg rejection, & flat-portfolio withdraw
//! 12. External `matcher.so` AMM single-signer fills (two takers, spread & LP withdrawal)
//! 13. Insurance LP deposits, pro-rata trading-fee yield, OI-gated withdraw, & exact redemption
//! 14. Market wind-down lifecycle: block opens, voluntary close, force-close, resolve, claim, tombstone

use super::*;

/// Isolated fresh DEX + USDC mint + optional markets/traders harness for boring tests.
struct BoringEnv {
    svm: LiteSVM,
    prog_id: Address,
    payer: Keypair,
    admin: Keypair,
    oracle: Keypair,
    mint: Address,
    fee_vault: Address,
    dex: Address,
    dex_vault: Address,
    slot: u64,
    markets: Vec<Address>,
    portfolios: Vec<Address>,
}

struct Trader {
    kp: Keypair,
    tok: Address,
    pfl: Address,
    init_spl: u64,
}

impl BoringEnv {
    fn new(elf: &[u8]) -> Self {
        let mut svm = LiteSVM::new();
        let prog_id = Keypair::new().pubkey();
        svm.add_program(prog_id, elf).expect("ELF load failed");
        let slot = 100u64;
        set_slot(&mut svm, slot);

        let payer = Keypair::new();
        let admin = Keypair::new();
        let oracle = Keypair::new();
        for kp in [&payer, &admin, &oracle] {
            svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
        }

        let mint = Keypair::new().pubkey();
        svm.set_account(
            mint,
            Account {
                lamports: 10_000_000,
                data: make_spl_mint(6, 100_000_000_000_000, &admin.pubkey()),
                owner: TOKEN_PROGRAM_ID,
                executable: false,
                rent_epoch: 0,
            },
        )
        .unwrap();

        let fee_vault = create_tok_acc(&mut svm, &mint, &admin.pubkey(), 0);
        let dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (dex_vault, bump) = derive_dex_vault(&prog_id, &dex);

        send_ok(
            &mut svm,
            ix_init_dex(
                prog_id,
                dex,
                admin.pubkey(),
                mint,
                dex_vault,
                fee_vault,
                TOKEN_PROGRAM_ID,
                SYSTEM_PROGRAM_ID,
                bump,
                6,
                0,
                SPL_TOKEN_RENT_MIN,
            ),
            &payer,
            &[&payer, &admin],
        );

        Self {
            svm,
            prog_id,
            payer,
            admin,
            oracle,
            mint,
            fee_vault,
            dex,
            dex_vault,
            slot,
            markets: Vec::new(),
            portfolios: Vec::new(),
        }
    }

    fn advance_slot(&mut self, delta: u64) {
        self.slot += delta;
        set_slot(&mut self.svm, self.slot);
    }

    fn create_market(
        &mut self,
        init_price: u64,
        exit_window: u64,
        im_bps: u64,
        mm_bps: u64,
        liq_fee_bps: u64,
        trade_fee_bps: u64,
        max_move_bps: u64,
    ) -> Address {
        // Clamp legacy test max_move_bps into the exact Solana K=4 compounding leader-window budget
        // (`4*m + ceil(m^2/1000) + liqFeeBps <= mmBps`) — e.g. `95` bps for `mm=500, liqFee=100`!
        let mut safe_move = max_move_bps.min(2500);
        while 4 * safe_move + (safe_move * safe_move + 999) / 1000 + liq_fee_bps > mm_bps && safe_move > 1 {
            safe_move -= 1;
        }
        let mkt = create_prog_acc(&mut self.svm, &self.prog_id, MKT_SIZE);
        let creator_tok = create_tok_acc(&mut self.svm, &self.mint, &self.admin.pubkey(), 0);
        send_ok(
            &mut self.svm,
            ix_create_market(
                self.prog_id,
                self.dex,
                mkt,
                self.mint,
                self.oracle.pubkey(),
                self.admin.pubkey(),
                creator_tok,
                self.fee_vault,
                init_price,
                exit_window,
                50, // max_staleness
                0,  // warmup_slots (instant realization)
                im_bps,
                mm_bps,
                liq_fee_bps,
                trade_fee_bps,
                safe_move,
                2500, // max_ins_draw_bps
                1_000_000 * POS_SCALE,
            ),
            &self.payer,
            &[&self.payer, &self.admin],
        );
        self.markets.push(mkt);
        mkt
    }

    fn create_trader(&mut self, init_spl: u64, deposit_amt: u64) -> Trader {
        let kp = Keypair::new();
        self.svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
        let tok = create_tok_acc(&mut self.svm, &self.mint, &kp.pubkey(), init_spl);
        let pfl = create_prog_acc(&mut self.svm, &self.prog_id, PFL_SIZE);
        send_ok(
            &mut self.svm,
            ix_init_portfolio(self.prog_id, self.dex, pfl, kp.pubkey()),
            &self.payer,
            &[&self.payer, &kp],
        );
        if deposit_amt > 0 {
            send_ok(
                &mut self.svm,
                ix_deposit_collateral(
                    self.prog_id,
                    self.dex,
                    pfl,
                    kp.pubkey(),
                    tok,
                    self.mint,
                    self.dex_vault,
                    TOKEN_PROGRAM_ID,
                    deposit_amt,
                ),
                &self.payer,
                &[&self.payer, &kp],
            );
        }
        self.portfolios.push(pfl);
        Trader {
            kp,
            tok,
            pfl,
            init_spl,
        }
    }

    fn deposit(&mut self, t: &Trader, amount: u64) {
        send_ok(
            &mut self.svm,
            ix_deposit_collateral(
                self.prog_id,
                self.dex,
                t.pfl,
                t.kp.pubkey(),
                t.tok,
                self.mint,
                self.dex_vault,
                TOKEN_PROGRAM_ID,
                amount,
            ),
            &self.payer,
            &[&self.payer, &t.kp],
        );
    }

    fn withdraw(&mut self, t: &Trader, amount: u64) {
        send_ok(
            &mut self.svm,
            ix_withdraw_collateral(
                self.prog_id,
                self.dex,
                t.pfl,
                t.kp.pubkey(),
                t.tok,
                self.mint,
                self.dex_vault,
                TOKEN_PROGRAM_ID,
                amount,
            ),
            &self.payer,
            &[&self.payer, &t.kp],
        );
    }

    fn withdraw_all(&mut self, t: &Trader) -> u64 {
        let cap = self.capital(t);
        if cap > 0 {
            self.withdraw(t, cap);
        }
        cap
    }

    fn update_oracle(&mut self, mkt: Address, target_price: u64, fund_sign: u8, fund_e6: u64) {
        let max_move_bps = read_u64(&self.svm, &mkt, 192);
        let mut cur_price = read_u64(&self.svm, &mkt, 112);
        loop {
            let max_allowed = ((cur_price as u128 * max_move_bps as u128) / 10_000u128) as u64;
            let diff = cur_price.abs_diff(target_price);
            if diff + fund_e6 <= max_allowed {
                self.advance_slot(1);
                send_ok(
                    &mut self.svm,
                    ix_update_oracle(
                        self.prog_id,
                        mkt,
                        self.oracle.pubkey(),
                        target_price,
                        fund_sign,
                        fund_e6,
                    ),
                    &self.payer,
                    &[&self.payer, &self.oracle],
                );
                break;
            }
            let step = diff.min(max_allowed.max(1));
            let next_p = if target_price >= cur_price {
                cur_price + step
            } else {
                cur_price - step
            };
            self.advance_slot(1);
            send_ok(
                &mut self.svm,
                ix_update_oracle(self.prog_id, mkt, self.oracle.pubkey(), next_p, 0, 0),
                &self.payer,
                &[&self.payer, &self.oracle],
            );
            cur_price = next_p;
        }
    }

    fn refresh(&mut self, mkt: Address, t: &Trader) {
        send_ok(
            &mut self.svm,
            ix_refresh_leg(self.prog_id, self.dex, mkt, t.pfl, false),
            &self.payer,
            &[&self.payer],
        );
    }

    fn trade(&mut self, mkt: Address, long_t: &Trader, short_t: &Trader, mode: u8, qty: u64) {
        self.trade_ext(mkt, long_t, short_t, mode, qty, 0);
    }

    fn trade_ext(
        &mut self,
        mkt: Address,
        long_t: &Trader,
        short_t: &Trader,
        mode: u8,
        qty: u64,
        exec_price: u64,
    ) {
        send_ok(
            &mut self.svm,
            ix_trade_ext(
                self.prog_id,
                self.dex,
                mkt,
                long_t.pfl,
                long_t.kp.pubkey(),
                short_t.pfl,
                short_t.kp.pubkey(),
                mode,
                qty,
                exec_price,
            ),
            &self.payer,
            &[&self.payer, &long_t.kp, &short_t.kp],
        );
    }

    fn capital(&self, t: &Trader) -> u64 {
        read_u64(&self.svm, &t.pfl, 88)
    }

    fn spl(&self, t: &Trader) -> u64 {
        token_amount(&self.svm, &t.tok)
    }

    fn oi_long(&self, mkt: Address) -> u64 {
        read_u64(&self.svm, &mkt, 256)
    }

    fn check(&self, label: &str) {
        assert_dex_invariants(
            &self.svm,
            &self.dex,
            &self.dex_vault,
            &self.markets,
            &self.portfolios,
            label,
        );
    }
}

/// 1. Boring deposit, partial withdraw, re-deposit, full withdraw, and CloseAccount rent reclaim.
pub fn test_boring_deposit_withdraw_roundtrip(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let alice = e.create_trader(1_000 * POS_SCALE, 0);
    e.check("t1-init");

    // Zero deposit and zero withdraw rejected with InvalidParams (103)
    send_err_custom(
        &mut e.svm,
        ix_deposit_collateral(
            e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 0,
        ),
        &e.payer,
        &[&e.payer, &alice.kp],
        103,
        "zero deposit",
    );
    send_err_custom(
        &mut e.svm,
        ix_withdraw_collateral(
            e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 0,
        ),
        &e.payer,
        &[&e.payer, &alice.kp],
        103,
        "zero withdraw",
    );

    // Deposit $100
    e.deposit(&alice, 100 * POS_SCALE);
    assert_eq!(e.capital(&alice), 100 * POS_SCALE);
    assert_eq!(e.spl(&alice), 900 * POS_SCALE);
    e.check("t1-dep100");

    // Over-withdraw $101 rejected with InsufficientFunds (108)
    send_err_custom(
        &mut e.svm,
        ix_withdraw_collateral(
            e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 101 * POS_SCALE,
        ),
        &e.payer,
        &[&e.payer, &alice.kp],
        108,
        "over-withdraw",
    );

    // Partial withdraw $40 -> $60 left
    e.withdraw(&alice, 40 * POS_SCALE);
    assert_eq!(e.capital(&alice), 60 * POS_SCALE);
    assert_eq!(e.spl(&alice), 940 * POS_SCALE);
    e.check("t1-wdr40");

    // Re-deposit $25 -> $85
    e.deposit(&alice, 25 * POS_SCALE);
    assert_eq!(e.capital(&alice), 85 * POS_SCALE);
    assert_eq!(e.spl(&alice), 915 * POS_SCALE);
    e.check("t1-redep25");

    // Full withdraw $85 -> back to exact initial SPL balance
    e.withdraw_all(&alice);
    assert_eq!(e.capital(&alice), 0);
    assert_eq!(e.spl(&alice), alice.init_spl);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t1-wdr-all");

    // Close empty portfolio and reclaim lamports
    let dest = Keypair::new().pubkey();
    let lam_before = e.svm.get_account(&alice.pfl).unwrap().lamports;
    send_ok(
        &mut e.svm,
        ix_close_account(e.prog_id, alice.pfl, alice.kp.pubkey(), dest),
        &e.payer,
        &[&e.payer, &alice.kp],
    );
    assert_eq!(e.svm.get_account(&dest).unwrap().lamports, lam_before);
}

/// 2. Boring Long vs Short profit & loss with 10 bps trading fee and full SPL withdrawal.
pub fn test_boring_simple_long_short_profit_and_loss(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 10, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
    let bob = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);

    // Open 2 BTC @ $100 -> notional $200, 10 bps fee = $0.20 each ($0.40 total routed to market insurance!)
    e.trade(btc, &alice, &bob, 0, 2 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 2 * POS_SCALE);
    assert_eq!(e.capital(&alice), 99_800_000);
    assert_eq!(e.capital(&bob), 99_800_000);
    assert_eq!(read_u64(&e.svm, &btc, 224), 400_000); // market insurance = $0.40
    e.check("t2-open");

    // Rally $100 -> $103 (+$6 Long, -$6 Short)
    e.update_oracle(btc, 103 * POS_SCALE, 0, 0);

    // Close 2 BTC @ $103 (risk-reducing closes are fee-free!)
    e.trade(btc, &alice, &bob, 1, 2 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 0);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false)], &e.payer, &[&e.payer]);
    e.check("t2-close");

    // Exact micro-USDC accounting:
    // Alice: $100 - $0.20 (open fee) + $6.00 = $105.80
    // Bob:   $100 - $0.20 (open fee) - $6.00 = $93.80
    // Insurance: $0.40
    assert_eq!(e.capital(&alice), 105_800_000);
    assert_eq!(e.capital(&bob), 93_800_000);
    assert_eq!(read_u64(&e.svm, &btc, 224), 400_000);

    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    assert_eq!(e.spl(&alice), alice.init_spl + 5_800_000);
    assert_eq!(e.spl(&bob), bob.init_spl - 6_200_000);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 400_000); // exact retained insurance
    e.check("t2-final");
}

/// 3. Boring scale-in (+1 -> +3 BTC) and multi-step partial closes (3 -> 2 -> 1 -> 0 BTC).
pub fn test_boring_scale_in_and_partial_closes(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let bob = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);

    // Open 1 BTC @ $100
    e.trade(btc, &alice, &bob, 0, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 1 * POS_SCALE);

    // $100 -> $102 (+$2 on 1 BTC), scale in +2 BTC (now 3 BTC)
    e.update_oracle(btc, 102 * POS_SCALE, 0, 0);
    e.trade(btc, &alice, &bob, 0, 2 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 3 * POS_SCALE);
    e.check("t3-scale-in");

    // $102 -> $105 (+$3 * 3 = +$9), partial close 1 BTC (now 2 BTC)
    e.update_oracle(btc, 105 * POS_SCALE, 0, 0);
    e.trade(btc, &alice, &bob, 1, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 2 * POS_SCALE);
    e.check("t3-close1");

    // $105 -> $101 (-$4 * 2 = -$8), partial close 1 BTC (now 1 BTC)
    e.update_oracle(btc, 101 * POS_SCALE, 0, 0);
    e.trade(btc, &alice, &bob, 1, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 1 * POS_SCALE);
    e.check("t3-close2");

    // $101 -> $104 (+$3 * 1 = +$3), close final 1 BTC (now 0 BTC)
    e.update_oracle(btc, 104 * POS_SCALE, 0, 0);
    e.trade(btc, &alice, &bob, 1, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 0);

    // Refresh both to sweep any remaining realized posPnl into capital
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false)], &e.payer, &[&e.payer]);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, false)], &e.payer, &[&e.payer]);
    e.check("t3-flat");

    // Net PnL = +2 + 9 - 8 + 3 = +$6.00 exact!
    assert_eq!(e.capital(&alice), 206 * POS_SCALE);
    assert_eq!(e.capital(&bob), 194 * POS_SCALE);

    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    assert_eq!(e.spl(&alice), alice.init_spl + 6 * POS_SCALE);
    assert_eq!(e.spl(&bob), bob.init_spl - 6 * POS_SCALE);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t3-final");
}

/// 4. Boring position flip: Alice Long 2 BTC (+$8) -> flat -> Short 3 BTC (+$12) = +$20 exact.
pub fn test_boring_position_flip_long_to_short(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let bob = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);

    // Phase 1: Alice Long 2 BTC @ $100 -> close @ $104 (+$8)
    e.trade(btc, &alice, &bob, 0, 2 * POS_SCALE);
    e.update_oracle(btc, 104 * POS_SCALE, 0, 0);
    e.trade(btc, &alice, &bob, 1, 2 * POS_SCALE);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false)], &e.payer, &[&e.payer]);
    assert_eq!(e.capital(&alice), 208 * POS_SCALE);
    assert_eq!(e.capital(&bob), 192 * POS_SCALE);
    e.check("t4-phase1");

    // Phase 2: Flip! Bob Long 3 BTC / Alice Short 3 BTC @ $104 -> close @ $100 (+$12 for Alice)
    e.trade(btc, &bob, &alice, 0, 3 * POS_SCALE);
    e.update_oracle(btc, 100 * POS_SCALE, 0, 0);
    e.trade(btc, &bob, &alice, 1, 3 * POS_SCALE);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false)], &e.payer, &[&e.payer]);
    assert_eq!(e.oi_long(btc), 0);
    assert_eq!(e.capital(&alice), 220 * POS_SCALE);
    assert_eq!(e.capital(&bob), 180 * POS_SCALE);
    e.check("t4-phase2");

    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    assert_eq!(e.spl(&alice), alice.init_spl + 20 * POS_SCALE);
    assert_eq!(e.spl(&bob), bob.init_spl - 20 * POS_SCALE);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t4-final");
}

/// 5. Boring bid/ask `execPrice` spread fills & clamp rejections (`Custom(130)`).
pub fn test_boring_exec_price_bid_ask_spread(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    // maxMoveBps = 200 (2% -> [$98, $102] valid execPrice band at $100 mark)
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 200);
    let taker = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
    let maker = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);

    // Out-of-clamp execPrice ($102.50 > $102, $97.50 < $98) rejected with ExecPriceClamp (130)
    send_err_custom(
        &mut e.svm,
        ix_trade_ext(e.prog_id, e.dex, btc, taker.pfl, taker.kp.pubkey(), maker.pfl, maker.kp.pubkey(), 0, 2 * POS_SCALE, 102_500_000),
        &e.payer,
        &[&e.payer, &taker.kp, &maker.kp],
        130,
        "execPrice above clamp",
    );
    send_err_custom(
        &mut e.svm,
        ix_trade_ext(e.prog_id, e.dex, btc, taker.pfl, taker.kp.pubkey(), maker.pfl, maker.kp.pubkey(), 0, 2 * POS_SCALE, 97_500_000),
        &e.payer,
        &[&e.payer, &taker.kp, &maker.kp],
        130,
        "execPrice below clamp",
    );

    // Taker buys 2 BTC at ask $100.50 (+$0.50 spread -> Taker pays $1.00 directly to Maker)
    e.trade_ext(btc, &taker, &maker, 0, 2 * POS_SCALE, 100_500_000);
    assert_eq!(e.capital(&taker), 99 * POS_SCALE);
    assert_eq!(e.capital(&maker), 101 * POS_SCALE);
    e.check("t5-open-spread");

    // Taker closes Long 2 BTC selling at bid $99.50 (-$0.50 spread -> seller Taker pays $1.00 directly to buyer Maker!)
    e.trade_ext(btc, &taker, &maker, 1, 2 * POS_SCALE, 99_500_000);
    assert_eq!(e.capital(&taker), 98 * POS_SCALE);
    assert_eq!(e.capital(&maker), 102 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 0);
    e.check("t5-close-spread");

    // Also verify execPrice < markP ($99.50) pays Short -> Long ($1.00)
    e.trade_ext(btc, &taker, &maker, 0, 2 * POS_SCALE, 99_500_000);
    assert_eq!(e.capital(&taker), 99 * POS_SCALE);
    assert_eq!(e.capital(&maker), 101 * POS_SCALE);
    e.trade_ext(btc, &taker, &maker, 1, 2 * POS_SCALE, 100 * POS_SCALE);
    e.check("t5-final");
}

/// 6. Boring funding rates: 3 slots positive (longs pay shorts) + 2 slots negative (shorts pay longs).
pub fn test_boring_funding_rate_longs_pay_shorts_and_reverse(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
    let bob = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);

    e.trade(btc, &alice, &bob, 0, 2 * POS_SCALE);

    // 3 slots positive funding: $0.25/BTC/slot (fundSign=0 -> Long pays Short): 3 * 0.25 * 2 = $1.50
    for _ in 0..3 {
        e.update_oracle(btc, 100 * POS_SCALE, 0, 250_000);
    }
    // 2 slots negative funding: $0.20/BTC/slot (fundSign=1 -> Short pays Long): 2 * 0.20 * 2 = $0.80
    for _ in 0..2 {
        e.update_oracle(btc, 100 * POS_SCALE, 1, 200_000);
    }

    // Close 2 BTC and refresh both -> net transfer = $1.50 - $0.80 = $0.70 from Alice to Bob!
    e.trade(btc, &alice, &bob, 1, 2 * POS_SCALE);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false)], &e.payer, &[&e.payer]);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, false)], &e.payer, &[&e.payer]);
    e.check("t6-closed");

    assert_eq!(e.capital(&alice), 99_300_000);
    assert_eq!(e.capital(&bob), 100_700_000);

    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    assert_eq!(e.spl(&alice), alice.init_spl - 700_000);
    assert_eq!(e.spl(&bob), bob.init_spl + 700_000);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t6-final");
}

/// 7. Boring multi-trader exit order permutations:
///    5 traders (Longs: Alice 2, Carol 3, Eve 1 vs Shorts: Bob 4, Dave 2) @ $100 -> $104.
///    Runs 3 distinct exit orderings (winners-first, reverse/smallest-first, and L->L / S->S hand-offs)
///    and asserts ALL 5 traders receive IDENTICAL final micro-USDC SPL balances across every ordering!
pub fn test_boring_exit_orders_permutations(elf: &[u8]) {
    let run_order = |order_kind: u8| -> [u64; 5] {
        let mut e = BoringEnv::new(elf);
        let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
        let alice = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
        let carol = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
        let eve   = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
        let bob   = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
        let dave  = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);

        // Open identical positions: Longs (Alice 2, Carol 3, Eve 1) vs Shorts (Bob 4, Dave 2)
        e.trade(btc, &alice, &bob,  0, 2 * POS_SCALE);
        e.trade(btc, &carol, &bob,  0, 2 * POS_SCALE);
        e.trade(btc, &carol, &dave, 0, 1 * POS_SCALE);
        e.trade(btc, &eve,   &dave, 0, 1 * POS_SCALE);
        assert_eq!(e.oi_long(btc), 6 * POS_SCALE);
        e.check("t7-opened");

        // Price moves $100 -> $104 (+$4/BTC)
        e.update_oracle(btc, 104 * POS_SCALE, 0, 0);

        match order_kind {
            0 => {
                // Order A: Biggest winners exit first (Carol 3 -> Alice 2 -> Eve 1)
                e.trade(btc, &carol, &bob,  1, 3 * POS_SCALE);
                e.check("t7-A-1");
                e.trade(btc, &alice, &dave, 1, 2 * POS_SCALE);
                e.check("t7-A-2");
                e.trade(btc, &eve,   &bob,  1, 1 * POS_SCALE);
                e.check("t7-A-3");
            }
            1 => {
                // Order B: Reverse / smallest-first fragmented closes
                e.trade(btc, &eve,   &dave, 1, 1 * POS_SCALE);
                e.check("t7-B-1");
                e.trade(btc, &alice, &dave, 1, 1 * POS_SCALE);
                e.check("t7-B-2");
                e.trade(btc, &alice, &bob,  1, 1 * POS_SCALE);
                e.check("t7-B-3");
                e.trade(btc, &carol, &bob,  1, 3 * POS_SCALE);
                e.check("t7-B-4");
            }
            _ => {
                // Order C: Same-side hand-offs (`mode=2` L->L & `mode=3` S->S) before closing!
                // Eve hands off Long(1) to Alice (mode=2: exiting=Eve, incoming=Alice)
                e.trade(btc, &eve, &alice, 2, 1 * POS_SCALE);
                assert_eq!(e.oi_long(btc), 6 * POS_SCALE, "L->L handoff preserves OI");
                e.check("t7-C-handoff-L");
                // Dave hands off Short(2) to Bob (mode=3: exiting=Dave, incoming=Bob)
                e.trade(btc, &dave, &bob, 3, 2 * POS_SCALE);
                assert_eq!(e.oi_long(btc), 6 * POS_SCALE, "S->S handoff preserves OI");
                e.check("t7-C-handoff-S");
                // Now Alice holds Long(3), Carol holds Long(3), Bob holds Short(6)
                e.trade(btc, &alice, &bob, 1, 3 * POS_SCALE);
                e.check("t7-C-close1");
                e.trade(btc, &carol, &bob, 1, 3 * POS_SCALE);
                e.check("t7-C-close2");
            }
        }

        assert_eq!(e.oi_long(btc), 0);
        // Settle any remaining posPnl on all 5 portfolios (order-independent!)
        for t in [&alice, &carol, &eve, &bob, &dave] {
            let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, t.pfl, false)], &e.payer, &[&e.payer]);
        }
        e.check("t7-settled");

        // Withdraw 100% of every trader's capital to SPL
        for t in [&alice, &carol, &eve, &bob, &dave] {
            e.withdraw_all(t);
        }
        assert_eq!(token_amount(&e.svm, &e.dex_vault), 0, "Vault must drain to exact 0");
        e.check("t7-drained");

        [e.spl(&alice), e.spl(&carol), e.spl(&eve), e.spl(&bob), e.spl(&dave)]
    };

    let res_a = run_order(0);
    let res_b = run_order(1);
    let res_c = run_order(2);

    let expected = [
        1_008 * POS_SCALE, // Alice (+$8)
        1_012 * POS_SCALE, // Carol (+$12)
        1_004 * POS_SCALE, // Eve   (+$4)
        984 * POS_SCALE,   // Bob   (-$16)
        992 * POS_SCALE,   // Dave  (-$8)
    ];
    assert_eq!(res_a, expected, "Order A exact SPL balances");
    assert_eq!(res_b, expected, "Order B must match Order A bit-for-bit!");
    assert_eq!(res_c, expected, "Order C (with L->L & S->S handoffs) must match Order A bit-for-bit!");
}

/// 8. Boring partial liquidation (restores health) followed by full liquidation (0 bad debt, 0 ADL).
pub fn test_boring_partial_and_full_liquidation_normal(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    // im = 10%, mm = 5%, liqFee = 1%, maxMove = 4%
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 15 * POS_SCALE);
    let bob = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let keeper_tok = create_tok_acc(&mut e.svm, &e.mint, &e.payer.pubkey(), 0);

    // Open 1 BTC @ $100 (IM = $10, MM = $5; Alice has $15)
    e.trade(btc, &alice, &bob, 0, 1 * POS_SCALE);

    // Healthy position cannot be liquidated -> PositionHealthy (116)
    send_err_custom(
        &mut e.svm,
        ix_liquidate_ext(e.prog_id, e.dex, btc, alice.pfl, keeper_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 0, 0, None),
        &e.payer,
        &[&e.payer],
        116,
        "healthy position liquidation rejected",
    );

    // Price drops $100 -> $96 -> $93 -> $90 -> $89 (each step <= 4% maxMoveBps; equity = $4.00 < MM $4.45!)
    e.update_oracle(btc, 96 * POS_SCALE, 0, 0);
    e.update_oracle(btc, 93 * POS_SCALE, 0, 0);
    e.update_oracle(btc, 90 * POS_SCALE, 0, 0);
    e.update_oracle(btc, 89 * POS_SCALE, 0, 0);

    // Partial liquidation of 0.5 BTC (`mode=0, req_qty=500_000`)
    send_ok(
        &mut e.svm,
        ix_liquidate_ext(e.prog_id, e.dex, btc, alice.pfl, keeper_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 0, 500_000, None),
        &e.payer,
        &[&e.payer],
    );
    assert_eq!(e.oi_long(btc), 500_000, "Partial liquidation leaves 0.5 BTC open");
    // Keeper earned exact 1% fee on 0.5 BTC @ $89 = ceil(44.50 * 100 / 10000) = $0.445
    assert_eq!(token_amount(&e.svm, &keeper_tok), 445_000);
    // Alice remaining capital = $4.00 - $0.445 = $3.555 > new MM (0.5 * $89 * 5% = $2.225)!
    assert_eq!(e.capital(&alice), 3_555_000);
    // In fallback mode=0 (no takeover counterparty), Bob's effective Short scales cleanly 1.0 -> 0.5 at $89 with 0 bad debt!
    assert_eq!(read_u64(&e.svm, &btc, 296), 500_000_000);
    e.check("t8-partial-liq");

    // Partial liquidation restored health -> another liquidation at $89 is REJECTED (116)!
    send_err_custom(
        &mut e.svm,
        ix_liquidate_ext(e.prog_id, e.dex, btc, alice.pfl, keeper_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 0, 0, None),
        &e.payer,
        &[&e.payer],
        116,
        "healthy after partial liquidation",
    );

    // Further drop $89 -> $86 -> $85: Alice equity = $3.555 - (0.5 * $4) = $1.555 < MM (0.5 * $85 * 5% = $2.125)!
    e.update_oracle(btc, 86 * POS_SCALE, 0, 0);
    e.update_oracle(btc, 85 * POS_SCALE, 0, 0);

    // Full liquidation (`req_qty = 0`)
    send_ok(
        &mut e.svm,
        ix_liquidate_ext(e.prog_id, e.dex, btc, alice.pfl, keeper_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 0, 0, None),
        &e.payer,
        &[&e.payer],
    );
    assert_eq!(e.oi_long(btc), 0, "Full liquidation closes remaining 0.5 BTC");

    // Bob clears dead leg and collects his profit ($11 on 1 BTC + ~$2 on 0.5 BTC = $13 total, <= 5 micro-units conservative floor dust across multi-slot clamped steps!)
    send_ok(&mut e.svm, ix_clear_dead_leg(e.prog_id, e.dex, btc, bob.pfl), &e.payer, &[&e.payer]);
    assert!(
        e.capital(&bob) >= 213 * POS_SCALE - 5 && e.capital(&bob) <= 213 * POS_SCALE,
        "Bob collects profit ($13 minus <=5 atoms conservative multi-step floor dust), got {}",
        e.capital(&bob)
    );
    // Alice withdraws leftover margin ($1.555 - $0.425 liq fee = $1.130)
    assert_eq!(e.capital(&alice), 1_130_000);
    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    let dust_res = read_u64(&e.svm, &btc, 216);
    assert!(dust_res <= 5, "Conservative multi-step floor dust <= 5 atoms, got {}", dust_res);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), dust_res);
    e.check("t8-final");
}

/// 9. Boring HLP-style liquidation takeover (`mode=1`):
///    HLP takes over Alice's underwater Long 2 BTC; OI/rawBasis/ADL are bit-for-bit invariant,
///    Bob's Short is 100% untouched, HLP collects bonus and exits cleanly on rebound!
pub fn test_boring_liquidation_takeover_hlp_style(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 25 * POS_SCALE);
    let bob   = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let hlp   = e.create_trader(1_000 * POS_SCALE, 500 * POS_SCALE);
    let liq_tok = create_tok_acc(&mut e.svm, &e.mint, &hlp.kp.pubkey(), 0);

    // Alice Long 2 BTC vs Bob Short 2 BTC @ $100
    e.trade(btc, &alice, &bob, 0, 2 * POS_SCALE);
    // Drop $100 -> $96 -> $93 -> $92 (each step <= 4%): Alice equity = $25 - $16 = $9.00 < MM (2 * $92 * 5% = $9.20)
    e.update_oracle(btc, 96 * POS_SCALE, 0, 0);
    e.update_oracle(btc, 93 * POS_SCALE, 0, 0);
    e.update_oracle(btc, 92 * POS_SCALE, 0, 0);

    let oi_l_pre = read_u64(&e.svm, &btc, 256);
    let oi_s_pre = read_u64(&e.svm, &btc, 264);
    let rl_pre   = read_u64(&e.svm, &btc, 272);
    let rs_pre   = read_u64(&e.svm, &btc, 280);
    let adll_pre = read_u64(&e.svm, &btc, 288);
    let adls_pre = read_u64(&e.svm, &btc, 296);

    // HLP executes full takeover (`mode=1, req_qty=0`) — fair gradual fee charges only feeFloor = maxFee/4 = $0.46!
    send_ok(
        &mut e.svm,
        ix_liquidate_ext(
            e.prog_id, e.dex, btc, alice.pfl, liq_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID,
            1, 0, Some((hlp.pfl, hlp.kp.pubkey())),
        ),
        &e.payer,
        &[&e.payer, &hlp.kp],
    );

    // ALL market OI / rawBasis / ADL fields must be BIT-FOR-BIT INVARIANT!
    assert_eq!(read_u64(&e.svm, &btc, 256), oi_l_pre);
    assert_eq!(read_u64(&e.svm, &btc, 264), oi_s_pre);
    assert_eq!(read_u64(&e.svm, &btc, 272), rl_pre);
    assert_eq!(read_u64(&e.svm, &btc, 280), rs_pre);
    assert_eq!(read_u64(&e.svm, &btc, 288), adll_pre);
    assert_eq!(read_u64(&e.svm, &btc, 296), adls_pre);
    // Gradual deficit-scaled liq fee: deficit=$0.20 < feeFloor=maxFee/4=$0.46 -> HLP gets $0.46, Alice keeps $8.54!
    assert_eq!(token_amount(&e.svm, &liq_tok), 460_000);
    assert_eq!(e.capital(&alice), 9_000_000 - 460_000);
    e.check("t9-takeover");

    // Price rebounds $92 -> $95 (+$6 for HLP, -$6 for Bob): HLP closes full 2 BTC vs Bob!
    e.update_oracle(btc, 95 * POS_SCALE, 0, 0);
    e.trade(btc, &hlp, &bob, 1, 2 * POS_SCALE);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, hlp.pfl, false)], &e.payer, &[&e.payer]);
    let _ = send_ixs_try(&mut e.svm, &[ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, false)], &e.payer, &[&e.payer]);
    assert_eq!(e.oi_long(btc), 0);
    assert_eq!(e.capital(&hlp), 506 * POS_SCALE, "HLP earns +$6 rebound PnL on full 2 BTC takeover");
    assert_eq!(e.capital(&bob), 210 * POS_SCALE, "Bob earns net +$10 ($100 -> $95 on 2 BTC Short)");
    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    e.withdraw_all(&hlp);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t9-final");
}

/// 10. Boring cross-margin multi-market offsetting (BTC + ETH) & instant realized-profit reuse!
pub fn test_boring_cross_margin_btc_eth_offset_and_profit_reuse(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let eth = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let sol = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 50 * POS_SCALE);
    let bob   = e.create_trader(1_000 * POS_SCALE, 500 * POS_SCALE);

    // Alice opens Long 1 BTC @ $100 AND Short 1 ETH @ $100 in ONE shared portfolio
    e.trade(btc, &alice, &bob, 0, 1 * POS_SCALE);
    e.trade(eth, &bob, &alice, 0, 1 * POS_SCALE);
    assert_eq!(read_u64(&e.svm, &alice.pfl, 104), 20 * POS_SCALE); // totalIm = $20
    e.check("t10-opened");

    // Correlated move: BTC -> $104 (+$4), ETH -> $104 (-$4)
    e.update_oracle(btc, 104 * POS_SCALE, 0, 0);
    e.update_oracle(eth, 104 * POS_SCALE, 0, 0);
    // Refresh Bob on BTC (funds realizedPool with $4) and Alice on both legs
    e.refresh(btc, &bob);
    e.refresh(btc, &alice);
    e.refresh(eth, &alice);
    assert_eq!(e.capital(&alice), 50 * POS_SCALE, "Correlated BTC (+$4) & ETH (-$4) net to exact $50");
    e.check("t10-offset");

    // BTC rallies further $104 -> $108 -> $112 -> $116 (+$12 more!) while ETH stays $104
    for p in [108, 112, 116] {
        e.update_oracle(btc, p * POS_SCALE, 0, 0);
    }
    e.refresh(btc, &bob);
    e.refresh(btc, &alice);
    // Alice's +$12 BTC profit auto-realized into shared capital WITHOUT closing BTC!
    assert_eq!(e.capital(&alice), 62 * POS_SCALE, "BTC profit auto-realized straight into shared capital");

    // Alice immediately reuses her realized profit to open a 3rd leg (Long 1 SOL @ $100) in ONE atomic bundle!
    let open_sol_ixs = vec![
        ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false),
        ix_refresh_leg(e.prog_id, e.dex, eth, alice.pfl, false),
        ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, false),
        ix_refresh_leg(e.prog_id, e.dex, eth, bob.pfl, false),
        ix_trade(e.prog_id, e.dex, sol, alice.pfl, alice.kp.pubkey(), bob.pfl, bob.kp.pubkey(), 0, 1 * POS_SCALE),
    ];
    send_ixs_ok(&mut e.svm, &open_sol_ixs, &e.payer, &[&e.payer, &alice.kp, &bob.kp]);
    assert_eq!(read_u8(&e.svm, &alice.pfl, 4), 3, "Alice now holds 3 active legs");
    // totalIm = 10%*(116 + 104 + 100) = $32.00; capital = $62.00 -> Alice can withdraw $30.00 excess right now!
    let wdr_ixs = vec![
        ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false),
        ix_refresh_leg(e.prog_id, e.dex, eth, alice.pfl, false),
        ix_refresh_leg(e.prog_id, e.dex, sol, alice.pfl, false),
        ix_withdraw_collateral(
            e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 30 * POS_SCALE,
        ),
    ];
    send_ixs_ok(&mut e.svm, &wdr_ixs, &e.payer, &[&e.payer, &alice.kp]);
    assert_eq!(e.capital(&alice), 32 * POS_SCALE);
    assert_eq!(e.spl(&alice), alice.init_spl - 20 * POS_SCALE); // deposited $50, withdrew $30 while keeping all 3 positions!
    e.check("t10-final");
}

/// 11. Boring withdrawal margin checks (`totalIm`), same-slot freshness (`Custom(122)`), & flat withdraw.
pub fn test_boring_withdraw_margin_checks_and_freshness(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
    let bob   = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);

    // Open Long 1 BTC @ $100 -> totalIm = $10
    e.trade(btc, &alice, &bob, 0, 1 * POS_SCALE);

    // Trying to withdraw $91 (leaving $9 < $10 totalIm) -> REJECTED InsufficientMargin (107)
    send_err_custom(
        &mut e.svm,
        ix_withdraw_collateral(
            e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 91 * POS_SCALE,
        ),
        &e.payer,
        &[&e.payer, &alice.kp],
        107,
        "withdraw below totalIm rejected",
    );

    // Withdrawing $90 (leaving exact $10 == totalIm) in same slot -> SUCCEEDS!
    e.withdraw(&alice, 90 * POS_SCALE);
    assert_eq!(e.capital(&alice), 10 * POS_SCALE);
    e.check("t11-wdr-at-im");

    // Re-deposit $5 and advance 1 slot -> leg is now stale
    e.deposit(&alice, 5 * POS_SCALE);
    e.advance_slot(1);

    // Bare Withdraw without RefreshLeg -> REJECTED StalePortfolioLeg (122)
    send_err_custom(
        &mut e.svm,
        ix_withdraw_collateral(
            e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE,
        ),
        &e.payer,
        &[&e.payer, &alice.kp],
        122,
        "stale withdraw rejected",
    );

    // Atomic [RefreshLeg, Withdraw] -> SUCCEEDS!
    send_ixs_ok(
        &mut e.svm,
        &[
            ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false),
            ix_withdraw_collateral(
                e.prog_id, e.dex, alice.pfl, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE,
            ),
        ],
        &e.payer,
        &[&e.payer, &alice.kp],
    );
    assert_eq!(e.capital(&alice), 10 * POS_SCALE);

    // Close position (flat, legCount == 0), advance 5 slots -> bare Withdraw works with NO RefreshLeg!
    e.trade(btc, &alice, &bob, 1, 1 * POS_SCALE);
    e.advance_slot(5);
    e.withdraw_all(&alice);
    assert_eq!(e.capital(&alice), 0);
    assert_eq!(e.spl(&alice), alice.init_spl);
    e.check("t11-final");
}

/// 12. Boring external `matcher.so` CPI-Out PropAMM single-signer fills (two takers + direct EOA LP withdrawal).
pub fn test_boring_matcher_amm_single_signer_fills(elf: &[u8], matcher_elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let matcher_prog = Keypair::new().pubkey();
    e.svm.add_program(matcher_prog, matcher_elf).expect("matcher ELF load failed");

    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let lp_owner = Keypair::new();
    e.svm.airdrop(&lp_owner.pubkey(), 10_000_000_000).unwrap();
    let lp_tok = create_tok_acc(&mut e.svm, &e.mint, &lp_owner.pubkey(), 2_000 * POS_SCALE);

    let prop_ctx = create_prog_acc(&mut e.svm, &matcher_prog, PROP_AMM_SIZE);
    let lp_pfl = create_prog_acc(&mut e.svm, &e.prog_id, PFL_SIZE);
    e.portfolios.push(lp_pfl);

    // InitPropAmm (Op 0): halfSpread=50bps, impact=10bps/unit, maxFill=10 BTC
    send_ok(
        &mut e.svm,
        ix_init_prop_amm(matcher_prog, prop_ctx, lp_owner.pubkey(), 0, 50, 10, 10 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    // LP keeps 100% EOA custody over `lp_pfl` and binds `prop_ctx` via `SetPortfolioMatcher`
    send_ok(&mut e.svm, ix_init_portfolio(e.prog_id, e.dex, lp_pfl, lp_owner.pubkey()), &e.payer, &[&e.payer, &lp_owner]);
    send_ok(&mut e.svm, ix_set_portfolio_matcher(e.prog_id, lp_pfl, lp_owner.pubkey(), Some(prop_ctx)), &e.payer, &[&e.payer, &lp_owner]);
    send_ok(
        &mut e.svm,
        ix_deposit_collateral(e.prog_id, e.dex, lp_pfl, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );

    let alice = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let carol = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);

    let (dex_addr, prog_id) = (e.dex, e.prog_id);
    let mk_fill = |t: &Trader, mode: u8, taker_is_long: bool, qty: u64, limit_p: u64| {
        ix_trade_with_matcher(
            prog_id, dex_addr, btc, t.pfl, t.kp.pubkey(), lp_pfl,
            matcher_prog, prop_ctx, None, mode, taker_is_long, qty, limit_p,
        )
    };

    // Single-signer Alice opens Long 1 BTC vs passive LP at Ask $100.60 (60 bps spread = $0.60!)
    send_ok(&mut e.svm, mk_fill(&alice, 0, true, 1 * POS_SCALE, 101 * POS_SCALE), &e.payer, &[&e.payer, &alice.kp]);
    assert_eq!(read_u64(&e.svm, &lp_pfl, 88), 1_000_600_000);
    assert_eq!(e.capital(&alice), 199_400_000);
    e.check("t12-alice-open");

    // Price moves $100 -> $102 (+$2 Alice, -$2 LP)
    e.update_oracle(btc, 102 * POS_SCALE, 0, 0);

    // Single-signer Alice closes Long 1 BTC selling at Bid $101.388 (60 bps of $102 = $0.612 -> LP earns spread!)
    send_ok(&mut e.svm, mk_fill(&alice, 1, true, 1 * POS_SCALE, 101 * POS_SCALE), &e.payer, &[&e.payer, &alice.kp]);
    assert_eq!(read_u64(&e.svm, &lp_pfl, 88), 999_212_000);
    // Single-signer Carol opens Short 1 BTC at Bid $101.388 and closes Short 1 BTC buying at Ask $102.612 (LP earns spread BOTH ways!)
    send_ok(&mut e.svm, mk_fill(&carol, 0, false, 1 * POS_SCALE, 101 * POS_SCALE), &e.payer, &[&e.payer, &carol.kp]);
    send_ok(&mut e.svm, mk_fill(&carol, 1, false, 1 * POS_SCALE, 103 * POS_SCALE), &e.payer, &[&e.payer, &carol.kp]);
    assert_eq!(e.oi_long(btc), 0);
    assert_eq!(read_u64(&e.svm, &lp_pfl, 88), 1_000_436_000);

    // LP withdraws $500 DIRECTLY via EOA `WithdrawCollateral` (ZERO PDA custody!)
    let lp_tok_pre = token_amount(&e.svm, &lp_tok);
    send_ok(
        &mut e.svm,
        ix_withdraw_collateral(e.prog_id, e.dex, lp_pfl, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    assert_eq!(token_amount(&e.svm, &lp_tok) - lp_tok_pre, 500 * POS_SCALE);
    e.check("t12-final");
}

/// 13. Boring Insurance LP lifecycle: LP1 deposits, earns trading fees, LP2 joins at higher NAV,
///     OI-gated withdraw rejection (`Custom(118)`), then pro-rata redemption to the exact micro-USDC!
pub fn test_boring_insurance_lp_deposit_fee_yield_withdraw(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    // 50 bps per side = 1.00% total notional fee -> routed to market insurance while totalInsShares > 0!
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 50, 400);

    let lp1 = Keypair::new();
    let lp2 = Keypair::new();
    e.svm.airdrop(&lp1.pubkey(), 10_000_000_000).unwrap();
    e.svm.airdrop(&lp2.pubkey(), 10_000_000_000).unwrap();
    let lp1_tok = create_tok_acc(&mut e.svm, &e.mint, &lp1.pubkey(), 1_000 * POS_SCALE);
    let lp2_tok = create_tok_acc(&mut e.svm, &e.mint, &lp2.pubkey(), 1_000 * POS_SCALE);
    let r1 = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    let r2 = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);

    // LP1 deposits $100 -> 100_000_000 shares
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, btc, r1, lp1.pubkey(), lp1_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp1],
    );
    assert_eq!(read_u64(&e.svm, &btc, 224), 100 * POS_SCALE);
    assert_eq!(read_u64(&e.svm, &r1, 80), 100 * POS_SCALE);

    // Alice & Bob open 20 BTC @ $100 ($2,000 notional -> $10 fee each = $20 total fee into insurance!)
    let alice = e.create_trader(2_000 * POS_SCALE, 500 * POS_SCALE);
    let bob   = e.create_trader(2_000 * POS_SCALE, 500 * POS_SCALE);
    e.trade(btc, &alice, &bob, 0, 20 * POS_SCALE);
    assert_eq!(read_u64(&e.svm, &btc, 224), 120 * POS_SCALE, "Insurance grew $100 -> $120 from open fees");
    e.check("t13-open-fees");

    // LP1 cannot withdraw while OI > 0 -> NonzeroOi (118)
    send_err_custom(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, btc, r1, lp1.pubkey(), lp1_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp1],
        118,
        "insurance withdraw blocked while OI > 0",
    );

    // LP2 deposits $60 at NAV $1.20/share -> mints exact 50 shares (totalShares = 150, ins = $180)
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, btc, r2, lp2.pubkey(), lp2_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 60 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp2],
    );
    assert_eq!(read_u64(&e.svm, &r2, 80), 50 * POS_SCALE);
    assert_eq!(read_u64(&e.svm, &btc, 224), 180 * POS_SCALE);
    e.check("t13-lp2-join");

    // Open another 10 BTC @ $100 -> +$10 fee ($5 each) -> ins = $190, then close all 30 BTC (fee-free closes) -> OI = 0!
    e.trade(btc, &alice, &bob, 0, 10 * POS_SCALE);
    assert_eq!(read_u64(&e.svm, &btc, 224), 190 * POS_SCALE);
    e.trade(btc, &alice, &bob, 1, 30 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 0);
    assert_eq!(read_u64(&e.svm, &btc, 224), 190 * POS_SCALE);

    // LP1 burns 100/150 shares -> floor(100 * 190 / 150) = $126.666666 (principal $100 + $26.666666 yield!)
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, btc, r1, lp1.pubkey(), lp1_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp1],
    );
    // LP2 burns remaining 50/50 shares -> exact $63.333334 (principal $60 + $3.333334 yield!)
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, btc, r2, lp2.pubkey(), lp2_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp2],
    );
    assert_eq!(read_u64(&e.svm, &btc, 224), 0);
    assert_eq!(token_amount(&e.svm, &lp1_tok), 1_000 * POS_SCALE + 26_666_666);
    assert_eq!(token_amount(&e.svm, &lp2_tok), 1_000 * POS_SCALE + 3_333_334);

    e.withdraw_all(&alice);
    e.withdraw_all(&bob);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t13-final");
}

/// 14. Boring full market wind-down lifecycle:
///     StartWindDown blocks opens -> voluntary close works during window -> ForceClosePair after window ->
///     ResolveMarket -> reverse-order ClaimResolved -> LP withdraws -> TombstoneMarket + CloseAccount!
pub fn test_boring_market_winddown_exit_orders_and_tombstone(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);

    let lp = Keypair::new();
    e.svm.airdrop(&lp.pubkey(), 10_000_000_000).unwrap();
    let lp_tok = create_tok_acc(&mut e.svm, &e.mint, &lp.pubkey(), 1_000 * POS_SCALE);
    let receipt = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, btc, receipt, lp.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp],
    );

    let alice = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
    let carol = e.create_trader(1_000 * POS_SCALE, 100 * POS_SCALE);
    let bob   = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);

    // Open: Alice Long 2, Carol Long 1, Bob Short 3 @ $100 -> rally to $103 (+$3/BTC)
    e.trade(btc, &alice, &bob, 0, 2 * POS_SCALE);
    e.trade(btc, &carol, &bob, 0, 1 * POS_SCALE);
    e.update_oracle(btc, 103 * POS_SCALE, 0, 0);

    // Market admin initiates WindDown (exitWindow = 10 slots)
    send_ok(&mut e.svm, ix_start_wind_down(e.prog_id, btc, e.admin.pubkey()), &e.payer, &[&e.payer, &e.admin]);

    // New opens are blocked during WindDown!
    send_err(
        &mut e.svm,
        ix_trade(e.prog_id, e.dex, btc, alice.pfl, alice.kp.pubkey(), bob.pfl, bob.kp.pubkey(), 0, 1 * POS_SCALE),
        &e.payer,
        &[&e.payer, &alice.kp, &bob.kp],
        "new opens blocked in wind-down",
    );

    // ForceClosePair BEFORE exitWindow expires is rejected!
    send_err(
        &mut e.svm,
        ix_force_close_pair(e.prog_id, e.dex, btc, alice.pfl, bob.pfl),
        &e.payer,
        &[&e.payer],
        "force-close before exitWindow expires",
    );

    // Voluntary close (mode=1) WORKS during exitWindow: Alice voluntarily closes 1 of her 2 BTC vs Bob
    e.trade(btc, &alice, &bob, 1, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 2 * POS_SCALE);
    e.check("t14-voluntary-close");

    // Advance past exitWindow (+12 slots) -> permissionless ForceClosePair closes remaining 2 BTC!
    e.advance_slot(12);
    send_ok(&mut e.svm, ix_force_close_pair(e.prog_id, e.dex, btc, alice.pfl, bob.pfl), &e.payer, &[&e.payer]);
    send_ok(&mut e.svm, ix_force_close_pair(e.prog_id, e.dex, btc, carol.pfl, bob.pfl), &e.payer, &[&e.payer]);
    assert_eq!(e.oi_long(btc), 0);
    e.check("t14-force-closed");

    // Permissionless ResolveMarket
    send_ok(&mut e.svm, ix_resolve_market(e.prog_id, e.dex, btc), &e.payer, &[&e.payer]);

    // Reverse-order ClaimResolved (Carol claims first, then Alice!)
    let _ = send_ixs_try(&mut e.svm, &[ix_claim_resolved(e.prog_id, e.dex, btc, carol.pfl)], &e.payer, &[&e.payer]);
    let _ = send_ixs_try(&mut e.svm, &[ix_claim_resolved(e.prog_id, e.dex, btc, alice.pfl)], &e.payer, &[&e.payer]);
    e.check("t14-claimed");

    assert_eq!(e.capital(&alice), 106 * POS_SCALE); // +$6 on 2 BTC
    assert_eq!(e.capital(&carol), 103 * POS_SCALE); // +$3 on 1 BTC
    assert_eq!(e.capital(&bob),   191 * POS_SCALE); // -$9 on 3 BTC

    // Everyone exits 100% cleanly (LP + all 3 traders)
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, btc, receipt, lp.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp],
    );
    assert_eq!(token_amount(&e.svm, &lp_tok), 1_000 * POS_SCALE);
    e.withdraw_all(&alice);
    e.withdraw_all(&carol);
    e.withdraw_all(&bob);
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 0);
    e.check("t14-drained");

    // TombstoneMarket + CloseAccount reclaims rent!
    send_ok(&mut e.svm, ix_tombstone_market(e.prog_id, btc), &e.payer, &[&e.payer]);
    let dest = Keypair::new().pubkey();
    send_ok(&mut e.svm, ix_close_account(e.prog_id, btc, e.admin.pubkey(), dest), &e.payer, &[&e.payer, &e.admin]);
    send_ok(&mut e.svm, ix_close_account(e.prog_id, receipt, lp.pubkey(), dest), &e.payer, &[&e.payer, &lp]);
    send_ok(&mut e.svm, ix_close_account(e.prog_id, alice.pfl, alice.kp.pubkey(), dest), &e.payer, &[&e.payer, &alice.kp]);
    assert_eq!(e.svm.get_account(&dest).unwrap().lamports, 30_000_000);
}

/// 15. Security regression suite for the 2026-11-26 mainnet exploit & all sibling vectors:
///     (a) Exact mainnet replay: `InitPortfolio` -> same-tx `[CloseAccount, refund, DepositInsurance]` -> REJECTED!
///     (b) Same-type revival: `InsReceipt` -> same-tx `[CloseAccount, refund, DepositInsurance]` -> REJECTED!
///     (c) `CloseAccount` writes `MAGIC_CLOSED ("DEAD")` and zeroes every residual byte `4..size`!
///     (d) Exact-size enforcement: oversized 952B `InsReceipt` / 952B `Market` -> REJECTED!
///     (e) Dirty-memory defense-in-depth: pre-filled `magic == 0` accounts with attacker pubkey/shares/capital
///         bytes get 100% zeroed by `DepositInsurance` & `InitPortfolio` (`shares == 1`, `capital == 0`)!
///     (f) `WithdrawInsurance` rejects any receipt with `shares > totalInsShares` (`Custom(119)`)!
pub fn test_security_revival_and_dirty_init_regressions(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);

    // Seed 70 USDC into BTC insurance (exact mainnet bounty setup!)
    let seed_lp = Keypair::new();
    e.svm.airdrop(&seed_lp.pubkey(), 10_000_000_000).unwrap();
    let seed_tok = create_tok_acc(&mut e.svm, &e.mint, &seed_lp.pubkey(), 70 * POS_SCALE);
    let seed_rec = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(
            e.prog_id, e.dex, btc, seed_rec, seed_lp.pubkey(), seed_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID,
            70 * POS_SCALE,
        ),
        &e.payer,
        &[&e.payer, &seed_lp],
    );
    assert_eq!(read_u64(&e.svm, &btc, 224), 70 * POS_SCALE);
    assert_eq!(read_u64(&e.svm, &btc, 248), 70 * POS_SCALE);

    // Attacker creates a 952-byte Portfolio (writing attacker pubkey bytes at 56..87, overlapping InsOff.shares 80..87!)
    let attacker = e.create_trader(10 * POS_SCALE, 0);
    let dest = Keypair::new().pubkey();

    // Helper: SystemProgram::Transfer(from, to, lamports)
    let sys_transfer = |from: Address, to: Address, lamports: u64| {
        let mut d = vec![0u8; 12];
        d[0..4].copy_from_slice(&2u32.to_le_bytes()); // SystemInstruction::Transfer = 2
        d[4..12].copy_from_slice(&lamports.to_le_bytes());
        Instruction {
            program_id: SYSTEM_PROGRAM_ID,
            accounts: vec![AccountMeta::new(from, true), AccountMeta::new(to, false)],
            data: d,
        }
    };

    // (a) Exact mainnet exploit replay: same-tx [CloseAccount(pfl), refund rent, DepositInsurance(receipt=pfl, 1)]
    //     MUST BE HARD-REJECTED (both exact-size mismatch AND MAGIC_CLOSED != 0)!
    send_ixs_err(
        &mut e.svm,
        &[
            ix_close_account(e.prog_id, attacker.pfl, attacker.kp.pubkey(), dest),
            sys_transfer(e.payer.pubkey(), attacker.pfl, 10_000_000),
            ix_deposit_insurance(
                e.prog_id, e.dex, btc, attacker.pfl, attacker.kp.pubkey(), attacker.tok,
                e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1,
            ),
        ],
        &e.payer,
        &[&e.payer, &attacker.kp],
        "mainnet exploit replay: Portfolio -> CloseAccount + refund -> DepositInsurance",
    );

    // (b) Same-type revival: close a real 88-byte InsReceipt + refund rent + re-DepositInsurance in SAME tx!
    let atk_rec = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(
            e.prog_id, e.dex, btc, atk_rec, attacker.kp.pubkey(), attacker.tok,
            e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1_000,
        ),
        &e.payer,
        &[&e.payer, &attacker.kp],
    );
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(
            e.prog_id, e.dex, btc, atk_rec, attacker.kp.pubkey(), attacker.tok,
            e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1_000,
        ),
        &e.payer,
        &[&e.payer, &attacker.kp],
    );
    send_ixs_err(
        &mut e.svm,
        &[
            ix_close_account(e.prog_id, atk_rec, attacker.kp.pubkey(), dest),
            sys_transfer(e.payer.pubkey(), atk_rec, 10_000_000),
            ix_deposit_insurance(
                e.prog_id, e.dex, btc, atk_rec, attacker.kp.pubkey(), attacker.tok,
                e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1,
            ),
        ],
        &e.payer,
        &[&e.payer, &attacker.kp],
        "same-tx InsReceipt revival after CloseAccount must fail (MAGIC_CLOSED != 0)",
    );

    // (c) Verify CloseAccount permanently writes MAGIC_CLOSED ("DEAD") and zeroes ALL bytes `4..size`!
    send_ixs_ok(
        &mut e.svm,
        &[
            ix_close_account(e.prog_id, attacker.pfl, attacker.kp.pubkey(), dest),
            sys_transfer(e.payer.pubkey(), attacker.pfl, 10_000_000), // keep alive to inspect closed bytes!
        ],
        &e.payer,
        &[&e.payer, &attacker.kp],
    );
    let closed_acc = e.svm.get_account(&attacker.pfl).unwrap();
    assert_eq!(
        &closed_acc.data[0..4],
        &0x44454144u32.to_le_bytes(),
        "CloseAccount must write permanent MAGIC_CLOSED (0x44454144)"
    );
    assert!(
        closed_acc.data[4..PFL_SIZE].iter().all(|&b| b == 0),
        "CloseAccount must zero EVERY byte in 4..PFL_SIZE"
    );
    // Attempting to InitPortfolio on the closed+refunded account MUST fail!
    send_err(
        &mut e.svm,
        ix_init_portfolio(e.prog_id, e.dex, attacker.pfl, attacker.kp.pubkey()),
        &e.payer,
        &[&e.payer, &attacker.kp],
        "InitPortfolio on closed+refunded account must fail",
    );

    // (d) Exact-size enforcement: oversized 952-byte Market and oversized 952-byte InsReceipt MUST fail!
    let big_ins = create_prog_acc(&mut e.svm, &e.prog_id, PFL_SIZE);
    send_err(
        &mut e.svm,
        ix_deposit_insurance(
            e.prog_id, e.dex, btc, big_ins, attacker.kp.pubkey(), attacker.tok,
            e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1,
        ),
        &e.payer,
        &[&e.payer, &attacker.kp],
        "oversized 952B InsReceipt rejected",
    );
    let big_mkt = create_prog_acc(&mut e.svm, &e.prog_id, PFL_SIZE);
    let ctok = create_tok_acc(&mut e.svm, &e.mint, &e.admin.pubkey(), 0);
    send_err(
        &mut e.svm,
        ix_create_market(
            e.prog_id, e.dex, big_mkt, e.mint, e.oracle.pubkey(), e.admin.pubkey(), ctok, e.fee_vault,
            100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE,
        ),
        &e.payer,
        &[&e.payer, &e.admin],
        "oversized 952B Market rejected",
    );

    // (e) Defense-in-depth: pre-dirty `magic == 0` buffers with the exact mainnet exploit value!
    let dirty_rec = Keypair::new().pubkey();
    let mut dirty_ins_data = vec![0xFFu8; INS_SIZE];
    dirty_ins_data[0..4].copy_from_slice(&0u32.to_le_bytes()); // magic == 0
    dirty_ins_data[80..88].copy_from_slice(&8_536_876_367_605_870_429u64.to_le_bytes());
    e.svm.set_account(
        dirty_rec,
        Account { lamports: 10_000_000, data: dirty_ins_data, owner: e.prog_id, executable: false, rent_epoch: 0 },
    ).unwrap();
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(
            e.prog_id, e.dex, btc, dirty_rec, attacker.kp.pubkey(), attacker.tok,
            e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1,
        ),
        &e.payer,
        &[&e.payer, &attacker.kp],
    );
    assert_eq!(read_u64(&e.svm, &dirty_rec, 80), 1, "Fresh DepositInsurance MUST zero dirty shares -> exact 1 share!");
    send_err_custom(
        &mut e.svm,
        ix_withdraw_insurance(
            e.prog_id, e.dex, btc, dirty_rec, attacker.kp.pubkey(), attacker.tok,
            e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 70 * POS_SCALE + 1,
        ),
        &e.payer,
        &[&e.payer, &attacker.kp],
        108,
        "attacker with 1 legitimate share cannot withdraw 70 USDC pot",
    );

    // Same dirty-buffer defense-in-depth on InitPortfolio (bytes 88..95 pre-filled with 999 USDC phantom capital!)
    let dirty_pfl = Keypair::new().pubkey();
    let mut dirty_pfl_data = vec![0xAAu8; PFL_SIZE];
    dirty_pfl_data[0..4].copy_from_slice(&0u32.to_le_bytes()); // magic == 0
    dirty_pfl_data[88..96].copy_from_slice(&(999 * POS_SCALE).to_le_bytes());
    e.svm.set_account(
        dirty_pfl,
        Account { lamports: 10_000_000, data: dirty_pfl_data, owner: e.prog_id, executable: false, rent_epoch: 0 },
    ).unwrap();
    send_ok(
        &mut e.svm,
        ix_init_portfolio(e.prog_id, e.dex, dirty_pfl, attacker.kp.pubkey()),
        &e.payer,
        &[&e.payer, &attacker.kp],
    );
    let init_pfl_acc = e.svm.get_account(&dirty_pfl).unwrap();
    assert_eq!(read_u64(&e.svm, &dirty_pfl, 88), 0, "InitPortfolio must zero dirty capital");
    assert_eq!(read_u64(&e.svm, &dirty_pfl, 96), 0, "InitPortfolio must zero dirty totalMm");
    assert_eq!(read_u64(&e.svm, &dirty_pfl, 104), 0, "InitPortfolio must zero dirty totalIm");
    assert!(init_pfl_acc.data[112..144].iter().all(|&b| b == 0), "InitPortfolio must zero dirty matcherCtx");
    assert!(init_pfl_acc.data[144..PFL_SIZE].iter().all(|&b| b == 0), "InitPortfolio must zero all 8 leg slots");

    // (f) WithdrawInsurance explicitly rejects any receipt with `shares > totalInsShares` (Custom(119))!
    let mut bogus_acc = e.svm.get_account(&dirty_rec).unwrap();
    bogus_acc.data[80..88].copy_from_slice(&(70 * POS_SCALE + 2).to_le_bytes());
    e.svm.set_account(dirty_rec, bogus_acc).unwrap();
    send_err_custom(
        &mut e.svm,
        ix_withdraw_insurance(
            e.prog_id, e.dex, btc, dirty_rec, attacker.kp.pubkey(), attacker.tok,
            e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 70 * POS_SCALE + 1,
        ),
        &e.payer,
        &[&e.payer, &attacker.kp],
        119,
        "WithdrawInsurance rejects receipt.shares > m.totalInsShares",
    );

    // Seed LP's 70 USDC insurance pot is 100% untouched!
    assert_eq!(token_amount(&e.svm, &e.dex_vault), 70 * POS_SCALE + 1);
}

/// 16. Audited Security Regressions across ALL 7 newly-hardened vectors:
///     (a) Permissionless `RefreshLeg(..., forceHaircut=1)` profit-wipe attack REJECTED!
///     (b) `Matcher::Fill` `mode=2/3` LP spread-drain & rogue-market fill REJECTED!
///     (c) `InitDex` with active `quoteMint` freeze authority REJECTED!
///     (d) Insurance share-pool attacks (`totSh=0 && ins>0` fee/donation capture, `<1 USDC` dust
///         first-LP deposit, drained-pool `totSh>0 && ins=0` revival) ALL REJECTED!
///     (e) SPL self-transfers (`destTok == vaultPda`, `liqTok == vaultPda`, `ownerTok == vaultPda`) REJECTED!
///     (f) Stale cross-leg spread payer in `Trade(mode=1, execPrice != markP)` REJECTED!
///     (g) Worthless `InsReceipt` (`shares > 0, ins == 0`) still burnable & rent-reclaimable AFTER `TombstoneMarket`!
pub fn test_audited_security_regressions(elf: &[u8], matcher_elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let matcher_prog = Keypair::new().pubkey();
    e.svm.add_program(matcher_prog, matcher_elf).expect("matcher ELF load failed");

    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let eth = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let bob   = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);

    // (a) Permissionless `RefreshLeg(..., forceHaircut=1)` profit-wipe attack MUST FAIL!
    //     Alice Short 10 BTC vs Bob Long 10 BTC at $100; BTC pumps +4% -> Bob gains +$40 while R_btc == 0.
    e.trade(btc, &bob, &alice, 0, 10 * POS_SCALE);
    e.update_oracle(btc, 104 * POS_SCALE, 0, 0);
    assert_eq!(read_u64(&e.svm, &btc, 216), 0, "R_btc must be 0 before losing Short settles");
    // 3-account permissionless RefreshLeg(forceHaircut=1) on Bob MUST fail!
    send_err(
        &mut e.svm,
        ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, true),
        &e.payer,
        &[&e.payer],
        "Permissionless RefreshLeg(forceHaircut=1) must fail",
    );
    // 4-account RefreshLeg(forceHaircut=1) signed by Alice (wrong owner!) MUST fail!
    send_err(
        &mut e.svm,
        ix_refresh_leg_signed(e.prog_id, e.dex, btc, bob.pfl, alice.kp.pubkey(), true),
        &e.payer,
        &[&e.payer, &alice.kp],
        "RefreshLeg(forceHaircut=1) signed by non-owner must fail",
    );
    // Normal permissionless RefreshLeg(forceHaircut=0) on Bob preserves his $40 posPnl intact!
    send_ok(&mut e.svm, ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, false), &e.payer, &[&e.payer]);
    assert_eq!(read_u64(&e.svm, &btc, 240), 40 * POS_SCALE, "Bob's $40 totalPosPnl must NOT be wiped");
    // Once Alice settles (-$40 into R_btc), Bob refreshes & receives 100% of his $40!
    send_ok(&mut e.svm, ix_refresh_leg(e.prog_id, e.dex, btc, alice.pfl, false), &e.payer, &[&e.payer]);
    send_ok(&mut e.svm, ix_refresh_leg(e.prog_id, e.dex, btc, bob.pfl, false), &e.payer, &[&e.payer]);
    assert_eq!(read_u64(&e.svm, &bob.pfl, 88), 240 * POS_SCALE, "Bob must receive full $40 profit");

    // (f) Stale-leg spread payer in Trade(mode=1, execPrice != markP) MUST FAIL!
    //     Open an ETH leg on Bob & Alice, advance slot & refresh ONLY BTC (leaving ETH stale),
    //     then try Trade(mode=1, BTC, execPrice=$106 > $104) where Bob pays spread while ETH is stale!
    e.trade(eth, &bob, &alice, 0, 2 * POS_SCALE);
    e.update_oracle(btc, 104 * POS_SCALE, 0, 0); // advances slot -> ETH leg is now stale!
    send_err(
        &mut e.svm,
        ix_trade_ext(e.prog_id, e.dex, btc, bob.pfl, bob.kp.pubkey(), alice.pfl, alice.kp.pubkey(), 1, 2 * POS_SCALE, 106 * POS_SCALE),
        &e.payer,
        &[&e.payer, &bob.kp, &alice.kp],
        "Trade(mode=1) with execPrice spread must reject stale second leg on spread payer",
    );
    // Close both legs cleanly at mark (0 spread)
    e.trade(btc, &bob, &alice, 1, 10 * POS_SCALE);
    e.trade(eth, &bob, &alice, 1, 2 * POS_SCALE);

    // (b) CPI-Out `TradeWithMatcher` rejects mode=2/3 hand-offs (`Custom(103)`), unauthorized
    //     `UpdatePropAmm` (`Custom(111)`), and directs spread strictly FROM taker TO LP on BOTH open & close!
    let lp_owner = Keypair::new();
    e.svm.airdrop(&lp_owner.pubkey(), 10_000_000_000).unwrap();
    let lp_tok = create_tok_acc(&mut e.svm, &e.mint, &lp_owner.pubkey(), 2_000 * POS_SCALE);
    let prop_ctx = create_prog_acc(&mut e.svm, &matcher_prog, PROP_AMM_SIZE);
    let lp_pfl = create_prog_acc(&mut e.svm, &e.prog_id, PFL_SIZE);
    e.portfolios.push(lp_pfl);
    send_ok(&mut e.svm, ix_init_prop_amm(matcher_prog, prop_ctx, lp_owner.pubkey(), 0, 100, 0, 10 * POS_SCALE), &e.payer, &[&e.payer, &lp_owner]);
    send_ok(&mut e.svm, ix_init_portfolio(e.prog_id, e.dex, lp_pfl, lp_owner.pubkey()), &e.payer, &[&e.payer, &lp_owner]);
    send_ok(&mut e.svm, ix_set_portfolio_matcher(e.prog_id, lp_pfl, lp_owner.pubkey(), Some(prop_ctx)), &e.payer, &[&e.payer, &lp_owner]);
    send_ok(
        &mut e.svm,
        ix_deposit_collateral(e.prog_id, e.dex, lp_pfl, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    let (dex_addr, prog_id) = (e.dex, e.prog_id);
    let mk_mfill = |mkt_addr: Address, mode: u8, qty: u64| {
        ix_trade_with_matcher(prog_id, dex_addr, mkt_addr, bob.pfl, bob.kp.pubkey(), lp_pfl, matcher_prog, prop_ctx, None, mode, true, qty, 0)
    };
    send_ok(&mut e.svm, mk_mfill(btc, 0, POS_SCALE), &e.payer, &[&e.payer, &bob.kp]);
    let lp_cap_after_open = read_u64(&e.svm, &lp_pfl, 88);
    assert!(lp_cap_after_open > 500 * POS_SCALE, "LP earned spread on open!");
    send_err_custom(&mut e.svm, mk_mfill(btc, 2, POS_SCALE), &e.payer, &[&e.payer, &bob.kp], 103, "TradeWithMatcher must reject mode=2 hand-off");
    send_err_custom(&mut e.svm, mk_mfill(btc, 3, POS_SCALE), &e.payer, &[&e.payer, &bob.kp], 103, "TradeWithMatcher must reject mode=3 hand-off");
    send_err_custom(&mut e.svm, ix_update_prop_amm(matcher_prog, prop_ctx, bob.kp.pubkey(), 1, 100, 0, POS_SCALE), &e.payer, &[&e.payer, &bob.kp], 111, "Non-owner UpdatePropAmm must fail");
    send_ok(&mut e.svm, mk_mfill(btc, 1, POS_SCALE), &e.payer, &[&e.payer, &bob.kp]);
    assert!(read_u64(&e.svm, &lp_pfl, 88) > lp_cap_after_open, "LP earned spread on reduce close too!");

    // (c) InitDex with active `quoteMint` freeze authority MUST FAIL (legacy #487)!
    let frozen_mint = Keypair::new().pubkey();
    let mut frozen_data = make_spl_mint(6, 100_000_000_000, &e.admin.pubkey());
    frozen_data[46..50].copy_from_slice(&1u32.to_le_bytes()); // COption::Some
    frozen_data[50..82].copy_from_slice(e.admin.pubkey().as_ref());
    e.svm.set_account(
        frozen_mint,
        Account { lamports: 10_000_000, data: frozen_data, owner: TOKEN_PROGRAM_ID, executable: false, rent_epoch: 0 },
    ).unwrap();
    let bad_dex = create_prog_acc(&mut e.svm, &e.prog_id, DEX_SIZE);
    let (bad_vault, bad_bump) = derive_dex_vault(&e.prog_id, &bad_dex);
    send_err(
        &mut e.svm,
        ix_init_dex(e.prog_id, bad_dex, e.admin.pubkey(), frozen_mint, bad_vault, e.fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, bad_bump, 6, 0, SPL_TOKEN_RENT_MIN),
        &e.payer,
        &[&e.payer, &e.admin],
        "InitDex must reject quoteMint with active freeze authority",
    );

    // (d) Insurance share-pool hardening:
    //     1. Dust first-LP deposit (`amount = 1 < 1_000_000`) on empty pool MUST fail!
    let r_dust = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_err(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, eth, r_dust, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 1),
        &e.payer,
        &[&e.payer, &lp_owner],
        "First insurance LP deposit < MIN_FIRST_INS_DEPOSIT must fail",
    );
    //     2. Donate $10 into ETH (`totSh == 0, ins == $10`), then LP deposits $5 (`>= MIN_FIRST_INS_DEPOSIT`):
    //        - Deposit MUST succeed (proves 1-atom permissionless donation CANNOT DoS future LPs!)
    //        - $10 donation is locked behind 10M unowned dead shares (`totSh = 15M`, `lpShares = 5M`)
    //        - Immediate full withdraw of all 5M shares pays EXACTLY $5 (0 donated funds captured!),
    //          leaving the $10 donation intact in ETH insurance!
    send_ok(
        &mut e.svm,
        ix_deposit_insurance_ext(e.prog_id, e.dex, eth, eth, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE, true),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    let lp_tok_before_dep = token_amount(&e.svm, &lp_tok);
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, eth, r_dust, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    assert_eq!(read_u64(&e.svm, &r_dust, 80), 5 * POS_SCALE, "LP must receive exactly 5M shares");
    assert_eq!(read_u64(&e.svm, &eth, 248), 15 * POS_SCALE, "totSh must lock 10M donated dead shares + 5M LP shares");
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, eth, r_dust, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    assert_eq!(token_amount(&e.svm, &lp_tok), lp_tok_before_dep, "LP withdrawing all shares must recover ONLY its $5 deposit (0 stolen donation!)");
    assert_eq!(read_u64(&e.svm, &eth, 224), 10 * POS_SCALE, "$10 donated insurance must remain 100% locked in market!");
    assert_eq!(read_u64(&e.svm, &eth, 248), 10 * POS_SCALE, "10M dead shares remain locking the $10 donation");
    //     3. Positive test: a second LP deposits $10 after the first LP exits -> mints exact 10M shares & recovers exact $10!
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, eth, r_dust, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    assert_eq!(read_u64(&e.svm, &r_dust, 80), 10 * POS_SCALE, "2nd LP must receive exact 10M shares");
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, eth, r_dust, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    assert_eq!(token_amount(&e.svm, &lp_tok), lp_tok_before_dep, "2nd LP recovers exact $10 principal");
    assert_eq!(read_u64(&e.svm, &eth, 224), 10 * POS_SCALE, "$10 donation still intact after 2nd LP round-trip");

    // (e) SPL self-transfer (`destTok == vaultPda`, `ownerTok == vaultPda`) MUST FAIL!
    send_err_custom(
        &mut e.svm,
        ix_withdraw_collateral(e.prog_id, e.dex, bob.pfl, bob.kp.pubkey(), e.dex_vault, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, POS_SCALE),
        &e.payer,
        &[&e.payer, &bob.kp],
        109,
        "WithdrawCollateral must reject destTok == vaultPda self-transfer",
    );
    send_err_custom(
        &mut e.svm,
        ix_deposit_collateral(e.prog_id, e.dex, bob.pfl, bob.kp.pubkey(), e.dex_vault, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, POS_SCALE),
        &e.payer,
        &[&e.payer, &bob.kp],
        109,
        "DepositCollateral must reject ownerTok == vaultPda self-transfer",
    );

    // (g) Drained pool (`totSh > 0, ins == 0`) blocks new LP deposit revival, AND worthless shares
    //     remain burnable + rent-reclaimable EVEN AFTER permissionless TombstoneMarket!
    let dead_mkt = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let r_lp1 = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_ok(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, dead_mkt, r_lp1, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    // Simulate market insurance drained to 0 while LP1 still holds 5_000_000 worthless shares
    // (keep Dex.totalInsurance & Dex.vaultBalance coherent by moving $5 to Dex.totalSurplus / resolved dust).
    let mut dm = e.svm.get_account(&dead_mkt).unwrap();
    dm.data[224..232].copy_from_slice(&0u64.to_le_bytes()); // MktOff.insurance = 0 (totSh still 5M!)
    e.svm.set_account(dead_mkt, dm).unwrap();
    let mut dx = e.svm.get_account(&e.dex).unwrap();
    let old_ti = u64::from_le_bytes(dx.data[176..184].try_into().unwrap());
    let old_ts = u64::from_le_bytes(dx.data[192..200].try_into().unwrap());
    dx.data[176..184].copy_from_slice(&(old_ti - 5 * POS_SCALE).to_le_bytes());
    dx.data[192..200].copy_from_slice(&(old_ts + 5 * POS_SCALE).to_le_bytes());
    e.svm.set_account(e.dex, dx).unwrap();

    // New LP2 attempting to deposit into drained pool (`totSh > 0, ins == 0`) MUST FAIL!
    let r_lp2 = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_err_custom(
        &mut e.svm,
        ix_deposit_insurance(e.prog_id, e.dex, dead_mkt, r_lp2, alice.kp.pubkey(), alice.tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE),
        &e.payer,
        &[&e.payer, &alice.kp],
        119,
        "DepositInsurance must reject drained pool with nonzero dead shares (totSh>0, ins=0)",
    );

    // Permissionless StartWindDown -> ResolveMarket -> TombstoneMarket succeeds even while r_lp1 has shares!
    send_ok(&mut e.svm, ix_start_wind_down(e.prog_id, dead_mkt, e.admin.pubkey()), &e.payer, &[&e.payer, &e.admin]);
    send_ok(&mut e.svm, ix_resolve_market(e.prog_id, e.dex, dead_mkt), &e.payer, &[&e.payer]);
    send_ok(&mut e.svm, ix_tombstone_market(e.prog_id, dead_mkt), &e.payer, &[&e.payer]);

    // LP1 burns worthless shares (`payout == 0`) EVEN ON TOMBSTONED MARKET, then closes InsReceipt for 100% rent!
    let tok_before = token_amount(&e.svm, &lp_tok);
    send_ok(
        &mut e.svm,
        ix_withdraw_insurance(e.prog_id, e.dex, dead_mkt, r_lp1, lp_owner.pubkey(), lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        &e.payer,
        &[&e.payer, &lp_owner],
    );
    assert_eq!(token_amount(&e.svm, &lp_tok), tok_before, "Worthless share burn must pay 0");
    assert_eq!(read_u64(&e.svm, &r_lp1, 80), 0, "InsReceipt shares must now be 0");
    let dest = Keypair::new().pubkey();
    e.svm.set_account(dest, Account { lamports: 1_000_000, data: vec![], owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut e.svm, ix_close_account(e.prog_id, r_lp1, lp_owner.pubkey(), dest), &e.payer, &[&e.payer, &lp_owner]);
    assert_eq!(e.svm.get_account(&dest).unwrap().lamports, 11_000_000, "LP1 must reclaim 100% InsReceipt rent after tombstone!");

    e.check("t16-final");
}

/// Test 17: I_m-contained cross-PnL fronting, optimistic LP NAV anti-arbitrage, Gap A bad-debt
///          write-off (no double-draw), SweepSurplus, and InitDex allowFreeze opt-in.
pub fn test_17_ins_fronting_lp_nav_sweep_and_freeze_flag(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);

    // 1. Create trusted cross-margin markets: MKT_A with `maxFrontBps = 10000` (100% of I_m) + BTC (`maxFrontBps = 0`)
    let admin_tok = create_tok_acc(&mut e.svm, &e.mint, &e.admin.pubkey(), 0);
    let mkt_a = create_prog_acc(&mut e.svm, &e.prog_id, MKT_SIZE);
    // Gap #1 LiteSVM regression: linear 4*100+100<=500 FAILS exact compounding K=4 check (`4*100+10+100=510 > 500`)!
    send_err_custom(
        &mut e.svm,
        ix_create_market(
            e.prog_id, e.dex, mkt_a, e.mint, e.oracle.pubkey(), e.admin.pubkey(), admin_tok, e.fee_vault,
            100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 100, 10_000, 1_000_000 * POS_SCALE,
        ),
        &e.payer, &[&e.payer, &e.admin], 103,
        "Gap #1: maxMove=100, liqFee=100, mm=500 must fail exact K=4 compounding check (510 > 500)",
    );
    // Gap #2a LiteSVM regression: maxFrontBps (5000) > maxInsDrawBps (2500) MUST fail with Custom(103)!
    let mut bad_front_ix = ix_create_market(
        e.prog_id, e.dex, mkt_a, e.mint, e.oracle.pubkey(), e.admin.pubkey(), admin_tok, e.fee_vault,
        100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 95, 2500, 1_000_000 * POS_SCALE,
    );
    bad_front_ix.data[2..4].copy_from_slice(&5000u16.to_le_bytes());
    send_err_custom(
        &mut e.svm, bad_front_ix, &e.payer, &[&e.payer, &e.admin], 103,
        "Gap #2: maxFrontBps > maxInsDrawBps must be rejected",
    );
    let mut cm_ix = ix_create_market(
        e.prog_id, e.dex, mkt_a, e.mint, e.oracle.pubkey(), e.admin.pubkey(), admin_tok, e.fee_vault,
        100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 95, 10_000, 1_000_000 * POS_SCALE,
    );
    cm_ix.data[2..4].copy_from_slice(&10_000u16.to_le_bytes()); // maxFrontBps = 10000 <= maxInsDrawBps = 10000
    send_ok(&mut e.svm, cm_ix, &e.payer, &[&e.payer, &e.admin]);
    e.markets.push(mkt_a);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 95);

    // Seed I_A with $50 from LP1 (50M shares) and I_BTC with $50 from LP1
    let lp1 = Keypair::new();
    e.svm.airdrop(&lp1.pubkey(), 1_000_000_000).unwrap();
    let lp1_tok = create_tok_acc(&mut e.svm, &e.mint, &lp1.pubkey(), 200 * POS_SCALE);
    let r_a1 = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    let r_btc1 = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_ok(&mut e.svm, ix_deposit_insurance(e.prog_id, e.dex, mkt_a, r_a1, lp1.pubkey(), lp1_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &e.payer, &[&e.payer, &lp1]);
    send_ok(&mut e.svm, ix_deposit_insurance(e.prog_id, e.dex, btc, r_btc1, lp1.pubkey(), lp1_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &e.payer, &[&e.payer, &lp1]);

    let alice = e.create_trader(200 * POS_SCALE, 100 * POS_SCALE);
    let bob   = e.create_trader(200 * POS_SCALE, 100 * POS_SCALE);

    // Alice Long 10 MKT_A vs Bob Short 10 MKT_A at $100 (notional $1,000, IM $100)
    e.trade(mkt_a, &alice, &bob, 0, 10 * POS_SCALE);

    // MKT_A moves +3% ($100 -> $103): Alice gains +$30, Bob loses -$30.
    // Crucially: Bob does NOT refresh yet -> R_A == 0!
    e.update_oracle(mkt_a, 103 * POS_SCALE, 0, 0);
    assert_eq!(read_u64(&e.svm, &mkt_a, 216), 0, "R_A must be 0 before Bob refreshes");

    // Alice refreshes FIRST: I_A fronts exact $30 into Alice.capital ($100 -> $130)!
    e.refresh(mkt_a, &alice);
    assert_eq!(e.capital(&alice), 130 * POS_SCALE, "Alice must receive $30 fronted from I_A immediately!");
    assert_eq!(read_u64(&e.svm, &mkt_a, 224), 20 * POS_SCALE, "I_A cash must drop $50 -> $20");
    assert_eq!(read_u64(&e.svm, &mkt_a, 232), 30 * POS_SCALE, "MktOff.insFronted must record $30 senior receivable");
    assert_eq!(read_u64(&e.svm, &btc, 224), 50 * POS_SCALE, "I_BTC must be 100% untouched");
    e.check("t17-after-front");

    // Alice immediately uses her fronted $30 cross-margin to open 2 BTC ($20 IM) on BTC/USD!
    // (Need fresh Bob leg on MKT_A before Bob opens BTC? Bob hasn't refreshed MKT_A in this slot;
    //  use Carol as BTC counterparty so Bob stays unrefreshed during LP arb check!)
    let carol_tr = e.create_trader(200 * POS_SCALE, 100 * POS_SCALE);
    e.trade(btc, &alice, &carol_tr, 0, 2 * POS_SCALE);
    e.check("t17-after-cross-btc-open");

    // ADVERSARIAL LP RECEIVABLE ARB CHECK:
    // While I_A cash = $20 and insFronted = $30 (optimistic NAV = $50, totSh = 50M),
    // Attacker Carol deposits $50 into DepositInsurance hoping to steal part of Bob's $30 repayment!
    let carol = Keypair::new();
    e.svm.airdrop(&carol.pubkey(), 1_000_000_000).unwrap();
    let carol_tok = create_tok_acc(&mut e.svm, &e.mint, &carol.pubkey(), 50 * POS_SCALE);
    let r_carol = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    send_ok(&mut e.svm, ix_deposit_insurance(e.prog_id, e.dex, mkt_a, r_carol, carol.pubkey(), carol_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &e.payer, &[&e.payer, &carol]);
    assert_eq!(read_u64(&e.svm, &r_carol, 80), 50 * POS_SCALE, "Carol MUST be priced at optimistic NAV ($20+$30=$50) -> 50M shares, NOT 125M!");

    // Now Bob refreshes MKT_A and pays $30 -> SENIOR REPAYMENT restores I_A ($70 -> $100) and clears insFronted ($30 -> $0)!
    e.refresh(mkt_a, &bob);
    assert_eq!(read_u64(&e.svm, &mkt_a, 232), 0, "Bob's $30 must repay insFronted to 0 senior!");
    assert_eq!(read_u64(&e.svm, &mkt_a, 224), 100 * POS_SCALE, "I_A must be fully restored to $100!");
    assert_eq!(read_u64(&e.svm, &mkt_a, 216), 0, "Exact $30 went to senior repayment, 0 excess to R_A");
    e.check("t17-after-senior-repay");

    // Close MKT_A positions so LPs can withdraw and verify Carol made $0 arbitrage profit!
    e.trade(mkt_a, &alice, &bob, 1, 10 * POS_SCALE);
    send_ok(&mut e.svm, ix_withdraw_insurance(e.prog_id, e.dex, mkt_a, r_carol, carol.pubkey(), carol_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &e.payer, &[&e.payer, &carol]);
    assert_eq!(token_amount(&e.svm, &carol_tok), 50 * POS_SCALE, "Carol must recover ONLY her $50 deposit ($0 receivable arb!)");
    assert_eq!(read_u64(&e.svm, &mkt_a, 224), 50 * POS_SCALE, "LP1's $50 must be 100% undiluted!");
    e.check("t17-after-arb-defeated");

    // 1b. GAP A TEST: Fronted bad-debt write-off (ZERO double-draw & ZERO overstated insFronted!)
    //     Open Long 10 MKT_A (Alice) vs Short 10 MKT_A (Bob2 with $10 cap after moving price? Open with $100 cap,
    //     pump MKT_A +12% over 3 slots so Bob2 loses $120 > $100 cap -> $20 bad debt!).
    //     Alice fronts first -> I_A drops by $120? I_A has $50, top up I_A by $100 -> $150.
    //     Alice fronts $120 (I_A: $150 -> $30, insFronted = $120).
    //     Keeper liquidates bankrupt Bob2: Bob2 pays $100 (I_A: $30 -> $130, insFronted: $120 -> $20),
    //     writeOffShortfall clears insFronted ($20 -> $0) and remShortfall = $0 -> I_A stays exact $130 & R_A == 0!
    {
        let lp_top = create_tok_acc(&mut e.svm, &e.mint, &lp1.pubkey(), 100 * POS_SCALE);
        send_ok(&mut e.svm, ix_deposit_insurance(e.prog_id, e.dex, mkt_a, r_a1, lp1.pubkey(), lp_top, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &e.payer, &[&e.payer, &lp1]);
        assert_eq!(read_u64(&e.svm, &mkt_a, 224), 150 * POS_SCALE);
        let a_win = e.create_trader(200 * POS_SCALE, 110 * POS_SCALE);
        let b_los = e.create_trader(200 * POS_SCALE, 103 * POS_SCALE);
        e.trade(mkt_a, &a_win, &b_los, 0, 10 * POS_SCALE); // at $103 -> IM=$103
        // Pump $103 -> $107 -> $111 -> $115 (+$12/unit = +$120 gain for a_win, -$120 loss for b_los -> $17 bad debt!)
        e.update_oracle(mkt_a, 107 * POS_SCALE, 0, 0);
        e.update_oracle(mkt_a, 111 * POS_SCALE, 0, 0);
        e.update_oracle(mkt_a, 115 * POS_SCALE, 0, 0);
        // Winner fronts $120 from I_A FIRST!
        e.refresh(mkt_a, &a_win);
        assert_eq!(e.capital(&a_win), 230 * POS_SCALE, "Winner fronted exact $120");
        assert_eq!(read_u64(&e.svm, &mkt_a, 224), 30 * POS_SCALE, "I_A cash $150 - $120 = $30");
        assert_eq!(read_u64(&e.svm, &mkt_a, 232), 120 * POS_SCALE, "insFronted == $120");
        // Keeper liquidates bankrupt b_los (only $103 capital vs $120 loss -> $17 bad debt!)
        let keep_tok = create_tok_acc(&mut e.svm, &e.mint, &e.admin.pubkey(), 0);
        send_ok(&mut e.svm, ix_liquidate(e.prog_id, e.dex, mkt_a, b_los.pfl, keep_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID), &e.payer, &[&e.payer]);
        assert_eq!(e.capital(&b_los), 0, "Bankrupt loser capital == 0");
        assert_eq!(read_u64(&e.svm, &mkt_a, 232), 0, "Gap A: uncollectible $17 written off -> insFronted == 0!");
        assert_eq!(read_u64(&e.svm, &mkt_a, 224), 133 * POS_SCALE, "Gap A: I_A == $150 - $17 = $133 (ZERO double-draw!)");
        assert_eq!(read_u64(&e.svm, &mkt_a, 216), 0, "Gap A: R_A == 0 (no stranded double-drawn funds!)");
        e.check("t17-gapA-bad-debt-writeoff");
    }

    // 1c. Gap #2b LiteSVM regression: cumulative NAV-based fronting cap blocks 2nd sequential front past maxFrontBps!
    //     Market has maxFrontBps = 2500, maxInsDrawBps = 2500, I_m = $200 (25% cap = $50).
    //     Winner 1 fronts $50 (I_m = $150, insFronted = $50). Winner 2 gains $10 and refreshes -> MUST NOT front!
    {
        let cap_mkt = create_prog_acc(&mut e.svm, &e.prog_id, MKT_SIZE);
        let mut cix = ix_create_market(
            e.prog_id, e.dex, cap_mkt, e.mint, e.oracle.pubkey(), e.admin.pubkey(), admin_tok, e.fee_vault,
            100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 95, 2500, 1_000_000 * POS_SCALE,
        );
        cix.data[2..4].copy_from_slice(&2500u16.to_le_bytes()); // maxFrontBps = 2500 == maxInsDrawBps
        send_ok(&mut e.svm, cix, &e.payer, &[&e.payer, &e.admin]);
        e.markets.push(cap_mkt);
        let r_cap = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
        let cap_lp_tok = create_tok_acc(&mut e.svm, &e.mint, &lp1.pubkey(), 200 * POS_SCALE);
        send_ok(&mut e.svm, ix_deposit_insurance(e.prog_id, e.dex, cap_mkt, r_cap, lp1.pubkey(), cap_lp_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &e.payer, &[&e.payer, &lp1]);
        let w1 = e.create_trader(300 * POS_SCALE, 200 * POS_SCALE);
        let w2 = e.create_trader(300 * POS_SCALE, 200 * POS_SCALE);
        let l1 = e.create_trader(500 * POS_SCALE, 400 * POS_SCALE);
        let l2 = e.create_trader(500 * POS_SCALE, 400 * POS_SCALE);
        e.trade(cap_mkt, &w1, &l1, 0, 10 * POS_SCALE); // w1 Long 10 vs l1
        e.trade(cap_mkt, &w2, &l2, 0, 10 * POS_SCALE); // w2 Long 10 vs l2 (distinct unrefreshed losers!)
        e.update_oracle(cap_mkt, 105 * POS_SCALE, 0, 0); // +$50 each for w1 & w2; neither loser settled!
        e.refresh(cap_mkt, &w1);
        assert_eq!(e.capital(&w1), 250 * POS_SCALE, "w1 fronts exact $50 (= 25% of $200 NAV)");
        assert_eq!(read_u64(&e.svm, &cap_mkt, 224), 150 * POS_SCALE, "I_m cash drops $200 -> $150");
        assert_eq!(read_u64(&e.svm, &cap_mkt, 232), 50 * POS_SCALE, "insFronted == $50 (exact 25% cap)");
        // Now w2 refreshes while insFronted == $50 (still unrepaid!):
        // Under old buggy formula `floor(150 * 25%) = $37.50`, w2 would front $37.50 pushing insFronted=$87.50 > $50!
        // Under fixed cumulative NAV cap `floor((150+50)*25%) - 50 = 0`, w2 MUST NOT front!
        let w2_cap_pre = e.capital(&w2);
        e.refresh(cap_mkt, &w2);
        assert_eq!(e.capital(&w2), w2_cap_pre, "Gap #2b: 2nd sequential front MUST be blocked once cumulative insFronted hits maxFrontBps of NAV!");
        assert_eq!(read_u64(&e.svm, &cap_mkt, 232), 50 * POS_SCALE, "Cumulative insFronted MUST stay <= 25% of NAV ($50)!");
        assert_eq!(read_u64(&e.svm, &cap_mkt, 224), 150 * POS_SCALE, "I_m cash MUST NOT be drained past maxFrontBps!");
        e.check("t17-gap2b-cumulative-nav-cap");
    }

    // 2. SweepSurplus: create $7 of real Dex.totalSurplus via a donated-only resolved market,
    //    verify non-admin & over-sweep are rejected, and admin sweeps exact $7 to feeVault!
    let dust_mkt = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let r_dust = create_prog_acc(&mut e.svm, &e.prog_id, INS_SIZE);
    let mut don_ix = ix_deposit_insurance(e.prog_id, e.dex, dust_mkt, r_dust, lp1.pubkey(), lp1_tok, e.mint, e.dex_vault, TOKEN_PROGRAM_ID, 7 * POS_SCALE);
    don_ix.data[9] = 1u8; // donate = 1 (byte 9 of 10-byte ix_deposit_insurance payload)
    send_ok(&mut e.svm, don_ix, &e.payer, &[&e.payer, &lp1]);
    send_ok(&mut e.svm, ix_start_wind_down(e.prog_id, dust_mkt, e.admin.pubkey()), &e.payer, &[&e.payer, &e.admin]);
    send_ok(&mut e.svm, ix_resolve_market(e.prog_id, e.dex, dust_mkt), &e.payer, &[&e.payer]);
    assert_eq!(read_u64(&e.svm, &e.dex, 192), 7 * POS_SCALE, "Resolved donated market must route $7 to Dex.totalSurplus");

    // Negative: non-admin cannot sweep surplus
    send_err_custom(&mut e.svm, ix_sweep_surplus(e.prog_id, e.dex, alice.kp.pubkey(), e.mint, e.dex_vault, e.fee_vault, TOKEN_PROGRAM_ID, 0), &e.payer, &[&e.payer, &alice.kp], 102, "non-admin SweepSurplus must fail");
    // Negative: admin cannot sweep > totalSurplus (user C+I+R 100% untouchable!)
    send_err_custom(&mut e.svm, ix_sweep_surplus(e.prog_id, e.dex, e.admin.pubkey(), e.mint, e.dex_vault, e.fee_vault, TOKEN_PROGRAM_ID, 8 * POS_SCALE), &e.payer, &[&e.payer, &e.admin], 103, "over-surplus SweepSurplus must fail");
    // Positive: admin sweeps exact $7 to feeVault
    let fv_before = token_amount(&e.svm, &e.fee_vault);
    send_ok(&mut e.svm, ix_sweep_surplus(e.prog_id, e.dex, e.admin.pubkey(), e.mint, e.dex_vault, e.fee_vault, TOKEN_PROGRAM_ID, 0), &e.payer, &[&e.payer, &e.admin]);
    assert_eq!(token_amount(&e.svm, &e.fee_vault), fv_before + 7 * POS_SCALE, "feeVault must receive exact $7 swept surplus");
    assert_eq!(read_u64(&e.svm, &e.dex, 192), 0, "Dex.totalSurplus must be 0 after full sweep");
    e.check("t17-after-sweep");

    // 3. InitDex `allowFreeze = 1` opt-in (mainnet USDC/USDT compatibility!)
    let mut frz_mint_data = vec![0u8; 82];
    frz_mint_data[44] = 6;
    frz_mint_data[45] = 1;
    frz_mint_data[46..50].copy_from_slice(&1u32.to_le_bytes()); // freeze_authority = Some(...)
    frz_mint_data[50..82].copy_from_slice(e.admin.pubkey().as_ref());
    let frz_mint = Keypair::new().pubkey();
    e.svm.set_account(frz_mint, Account { lamports: 10_000_000, data: frz_mint_data, owner: TOKEN_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
    let frz_dex = create_prog_acc(&mut e.svm, &e.prog_id, DEX_SIZE);
    let (frz_vault, frz_bump) = Address::find_program_address(&[b"dvlt", frz_dex.as_ref()], &e.prog_id);
    let frz_fee = create_tok_acc(&mut e.svm, &frz_mint, &e.admin.pubkey(), 0);
    let mut init_frz = ix_init_dex(e.prog_id, frz_dex, e.admin.pubkey(), frz_mint, frz_vault, frz_fee, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, frz_bump, 6, 0, 3_000_000);
    init_frz.data[3] = 1; // allowFreeze = 1 (explicit opt-in for mainnet USDC/USDT)
    send_ok(&mut e.svm, init_frz, &e.payer, &[&e.payer, &e.admin]);
    assert_eq!(read_u8(&e.svm, &frz_dex, 7), 1, "DexOff.allowFreeze must record 1 immutably");
}

/// 18. Round-3 regression: atomic auto-netted `Trade(mode=4)` (`tradeNettedCore`).
///     (a) mode=4 from flat opens like mode 0; (b) mutually offsetting positions net-close
///     atomically (closeB=closeS>0 -> mode-1 close), restoring OI to 0 with exact conservation.
pub fn test_round3_mode4_atomic_netting(elf: &[u8]) {
    let mut e = BoringEnv::new(elf);
    let btc = e.create_market(100 * POS_SCALE, 10, 1000, 500, 100, 0, 400);
    let alice = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);
    let bob   = e.create_trader(1_000 * POS_SCALE, 200 * POS_SCALE);

    // (a) mode=4 from flat == plain open: Alice long 1 vs Bob short 1
    e.trade(btc, &alice, &bob, 4, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 1 * POS_SCALE, "mode4 open: OI must be 1");
    assert_eq!(read_u8(&e.svm, &alice.pfl, 4), 1, "alice holds 1 leg after mode4 open");
    e.check("r3-mode4-open");

    // (b) mutually offsetting positions net-close atomically. Pass the SHORT holder first
    //     (buyer) and the LONG holder second (seller) so closeB = closeS = 1 under tradeNettedCore.
    e.trade(btc, &bob, &alice, 4, 1 * POS_SCALE);
    assert_eq!(e.oi_long(btc), 0, "mode4 netting close: OI must return to 0");
    assert_eq!(read_u8(&e.svm, &alice.pfl, 4), 0, "alice must be flat after netting");
    assert_eq!(read_u8(&e.svm, &bob.pfl, 4), 0, "bob must be flat after netting");
    e.check("r3-mode4-netted");
}

/// Runs all boring everyday exchange + security regression LiteSVM tests as Suite 12.
pub fn run_all_boring_tests(elf: &[u8], matcher_elf: &[u8]) {
    test_boring_deposit_withdraw_roundtrip(elf);
    test_boring_simple_long_short_profit_and_loss(elf);
    test_boring_scale_in_and_partial_closes(elf);
    test_boring_position_flip_long_to_short(elf);
    test_boring_exec_price_bid_ask_spread(elf);
    test_boring_funding_rate_longs_pay_shorts_and_reverse(elf);
    test_boring_exit_orders_permutations(elf);
    test_boring_partial_and_full_liquidation_normal(elf);
    test_boring_liquidation_takeover_hlp_style(elf);
    test_boring_cross_margin_btc_eth_offset_and_profit_reuse(elf);
    test_boring_withdraw_margin_checks_and_freshness(elf);
    test_boring_matcher_amm_single_signer_fills(elf, matcher_elf);
    test_boring_insurance_lp_deposit_fee_yield_withdraw(elf);
    test_boring_market_winddown_exit_orders_and_tombstone(elf);
    test_security_revival_and_dirty_init_regressions(elf);
    test_audited_security_regressions(elf, matcher_elf);
    test_17_ins_fronting_lp_nav_sweep_and_freeze_flag(elf);
    test_round3_mode4_atomic_netting(elf);
    println!("[PASS] Suite 12: 17 Boring Exchange & Audited Security Regression LiteSVM Tests (Deposits, Scale-In/Out,");
    println!("       Flips, Spreads, Funding, 3 Exit-Order Permutations, Partial+Full Liq, HLP Takeover, Cross-Margin Reuse,");
    println!("       AMM Matcher, LP Yield, WindDown, Revival/Dirty-Init, ForceHaircut, FreezeMint, SharePool, Self-Transfer,");
    println!("       I_m-Contained Cross-PnL Fronting, Optimistic LP NAV Anti-Arb, SweepSurplus & AllowFreeze Opt-In!)");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn load_elfs() -> (Vec<u8>, Vec<u8>) {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let elf = std::fs::read(root.join("build/percolator.so"))
            .expect("build/percolator.so missing — run ./scripts/build-and-test.sh first");
        let matcher_elf = std::fs::read(root.join("build/matcher.so"))
            .expect("build/matcher.so missing — run ./scripts/build-and-test.sh first");
        (elf, matcher_elf)
    }

    #[test] fn boring_01_deposit_withdraw_roundtrip() { let (e, _) = load_elfs(); test_boring_deposit_withdraw_roundtrip(&e); }
    #[test] fn boring_02_simple_long_short_pnl() { let (e, _) = load_elfs(); test_boring_simple_long_short_profit_and_loss(&e); }
    #[test] fn boring_03_scale_in_and_partial_closes() { let (e, _) = load_elfs(); test_boring_scale_in_and_partial_closes(&e); }
    #[test] fn boring_04_position_flip_long_to_short() { let (e, _) = load_elfs(); test_boring_position_flip_long_to_short(&e); }
    #[test] fn boring_05_exec_price_bid_ask_spread() { let (e, _) = load_elfs(); test_boring_exec_price_bid_ask_spread(&e); }
    #[test] fn boring_06_funding_rate_both_directions() { let (e, _) = load_elfs(); test_boring_funding_rate_longs_pay_shorts_and_reverse(&e); }
    #[test] fn boring_07_exit_orders_permutations() { let (e, _) = load_elfs(); test_boring_exit_orders_permutations(&e); }
    #[test] fn boring_08_partial_and_full_liquidation() { let (e, _) = load_elfs(); test_boring_partial_and_full_liquidation_normal(&e); }
    #[test] fn boring_09_liquidation_takeover_hlp_style() { let (e, _) = load_elfs(); test_boring_liquidation_takeover_hlp_style(&e); }
    #[test] fn boring_10_cross_margin_offset_and_profit_reuse() { let (e, _) = load_elfs(); test_boring_cross_margin_btc_eth_offset_and_profit_reuse(&e); }
    #[test] fn boring_11_withdraw_margin_checks_and_freshness() { let (e, _) = load_elfs(); test_boring_withdraw_margin_checks_and_freshness(&e); }
    #[test] fn boring_12_matcher_amm_single_signer_fills() { let (e, m) = load_elfs(); test_boring_matcher_amm_single_signer_fills(&e, &m); }
    #[test] fn boring_13_insurance_lp_deposit_yield_withdraw() { let (e, _) = load_elfs(); test_boring_insurance_lp_deposit_fee_yield_withdraw(&e); }
    #[test] fn boring_14_market_winddown_exit_and_tombstone() { let (e, _) = load_elfs(); test_boring_market_winddown_exit_orders_and_tombstone(&e); }
    #[test] fn boring_15_security_revival_and_dirty_init_regressions() { let (e, _) = load_elfs(); test_security_revival_and_dirty_init_regressions(&e); }
    #[test] fn boring_16_audited_security_regressions() { let (e, m) = load_elfs(); test_audited_security_regressions(&e, &m); }
    #[test] fn boring_17_ins_fronting_lp_nav_sweep_and_freeze_flag() { let (e, _) = load_elfs(); test_17_ins_fronting_lp_nav_sweep_and_freeze_flag(&e); }
    #[test] fn boring_18_round3_mode4_atomic_netting() { let (e, _) = load_elfs(); test_round3_mode4_atomic_netting(&e); }
}
