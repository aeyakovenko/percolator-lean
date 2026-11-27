mod boring_tests;

use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_clock::Clock;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_signer::Signer;
use solana_transaction::Transaction;

const TOKEN_PROGRAM_ID: Address =
    Address::from_str_const("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
const TOKEN_2022_PROGRAM_ID: Address =
    Address::from_str_const("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb");
const WSOL_MINT: Address =
    Address::from_str_const("So11111111111111111111111111111111111111112");
const SYSTEM_PROGRAM_ID: Address =
    Address::from_str_const("11111111111111111111111111111111");
const SPL_TOKEN_RENT_MIN: u64 = 2_039_280;

// Exact v2 layout constants matching Percolator/Layout.lean & Percolator/RewardModule.lean
const DEX_SIZE: usize = 208;
const MKT_SIZE: usize = 400;
const PFL_SIZE: usize = 976;
const INS_SIZE: usize = 88;
const REW_SIZE: usize = 400;
const EPOCH_SIZE: usize = 104;
const BID_SIZE: usize = 120;
const PROP_AMM_SIZE: usize = 272;
const HLP_SIZE: usize = 296;
const HLP_REC_SIZE: usize = 88;
const MAX_LEGS: usize = 8;
const LEG_HEADER: usize = 144;
const LEG_STRIDE: usize = 104;
const POS_SCALE: u64 = 1_000_000;
const ADL_ONE: u64 = 1_000_000_000;

fn make_spl_mint(decimals: u8, supply: u64, mint_auth: &Address) -> Vec<u8> {
    let mut data = vec![0u8; 82];
    data[0..4].copy_from_slice(&1u32.to_le_bytes());
    data[4..36].copy_from_slice(mint_auth.as_ref());
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = decimals;
    data[45] = 1;
    data
}

fn make_spl_token_account(mint: &Address, owner: &Address, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; 165];
    data[0..32].copy_from_slice(mint.as_ref());
    data[32..64].copy_from_slice(owner.as_ref());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1; // Initialized
    data
}

fn token_amount(svm: &LiteSVM, acc: &Address) -> u64 {
    let a = svm.get_account(acc).expect("token acc missing");
    u64::from_le_bytes(a.data[64..72].try_into().unwrap())
}

fn read_u64(svm: &LiteSVM, acc: &Address, off: usize) -> u64 {
    let a = svm.get_account(acc).expect("acc missing");
    u64::from_le_bytes(a.data[off..off + 8].try_into().unwrap())
}

fn read_u8(svm: &LiteSVM, acc: &Address, off: usize) -> u8 {
    let a = svm.get_account(acc).expect("acc missing");
    a.data[off]
}

fn pfl_free_capital(svm: &LiteSVM, pfl: &Address) -> u64 {
    read_u64(svm, pfl, 88)
}

fn pfl_locked_mm(svm: &LiteSVM, pfl: &Address) -> u64 {
    read_u64(svm, pfl, 16)
}

fn pfl_total_capital(svm: &LiteSVM, pfl: &Address) -> u64 {
    pfl_free_capital(svm, pfl) + pfl_locked_mm(svm, pfl)
}

fn leg_locked_mm_for_mkt(svm: &LiteSVM, pfl: &Address, mkt_id: u64) -> u64 {
    for idx in 0..MAX_LEGS {
        let base = LEG_HEADER + idx * LEG_STRIDE;
        if read_u8(svm, pfl, base) != 0 && read_u64(svm, pfl, base + 8) == mkt_id {
            return read_u64(svm, pfl, base + 96);
        }
    }
    0
}

fn set_slot(svm: &mut LiteSVM, slot: u64) {
    let mut clock: Clock = svm.get_sysvar();
    clock.slot = slot;
    svm.set_sysvar(&clock);
    svm.expire_blockhash();
}

fn get_slot(svm: &LiteSVM) -> u64 {
    let clock: Clock = svm.get_sysvar();
    clock.slot
}

fn compact_u16_len(n: usize) -> usize {
    if n < 0x80 { 1 } else if n < 0x4000 { 2 } else { 3 }
}

/// Exact Solana legacy wire transaction byte length (must be <= 1,232 bytes for UDP MTU!).
fn legacy_tx_wire_bytes(tx: &Transaction) -> usize {
    let sigs = tx.signatures.len();
    let msg = &tx.message;
    let keys = msg.account_keys.len();
    let ixs = &msg.instructions;
    let mut len = compact_u16_len(sigs) + sigs * 64;
    len += 3; // MessageHeader
    len += compact_u16_len(keys) + keys * 32;
    len += 32; // recent_blockhash
    len += compact_u16_len(ixs.len());
    for ix in ixs {
        len += 1; // program_id_index
        len += compact_u16_len(ix.accounts.len()) + ix.accounts.len();
        len += compact_u16_len(ix.data.len()) + ix.data.len();
    }
    len
}

fn send_ixs_ok_measured(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair]) -> (u64, usize) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(ixs, Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let wire = legacy_tx_wire_bytes(&tx);
    let res = svm.send_transaction(tx).unwrap_or_else(|e| panic!("Expected OK (wire={}B), got {:?}", wire, e));
    (res.compute_units_consumed, wire)
}

fn send_ixs_ok(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair]) -> u64 {
    send_ixs_ok_measured(svm, ixs, payer, signers).0
}

fn send_ok(svm: &mut LiteSVM, ix: Instruction, payer: &Keypair, signers: &[&Keypair]) -> u64 {
    send_ixs_ok(svm, &[ix], payer, signers)
}

fn send_ok_assert_log(
    svm: &mut LiteSVM,
    ix: Instruction,
    payer: &Keypair,
    signers: &[&Keypair],
    expected_prefix: &str,
) -> u64 {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx).unwrap_or_else(|e| panic!("Expected OK, got {:?}", e));
    assert!(
        res.logs.iter().any(|l| l.contains(expected_prefix)),
        "Expected structured log containing '{}' in logs: {:?}",
        expected_prefix,
        res.logs
    );
    res.compute_units_consumed
}

fn send_ixs_err(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair], label: &str) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(ixs, Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    assert!(res.is_err(), "Expected rejection for '{}', but tx succeeded!", label);
}

fn send_ixs_try(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair]) -> Result<u64, String> {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(ixs, Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    svm.send_transaction(tx)
        .map(|r| r.compute_units_consumed)
        .map_err(|e| format!("{:?}", e))
}

fn send_err(svm: &mut LiteSVM, ix: Instruction, payer: &Keypair, signers: &[&Keypair], label: &str) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    assert!(res.is_err(), "Expected rejection for '{}', but tx succeeded!", label);
}

fn send_err_custom(
    svm: &mut LiteSVM,
    ix: Instruction,
    payer: &Keypair,
    signers: &[&Keypair],
    expected_code: u32,
    label: &str,
) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    let err = res.expect_err(&format!(
        "Expected Custom({}) rejection for '{}', but tx SUCCEEDED!",
        expected_code, label
    ));
    let dbg = format!("{:?}", err);
    let needle = format!("Custom({})", expected_code);
    assert!(
        dbg.contains(&needle),
        "Expected {} for '{}', got: {}",
        needle,
        label,
        dbg
    );
}

fn create_prog_acc(svm: &mut LiteSVM, prog_id: &Address, size: usize) -> Address {
    let addr = Keypair::new().pubkey();
    svm.set_account(
        addr,
        Account {
            lamports: 10_000_000,
            data: vec![0u8; size],
            owner: *prog_id,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();
    addr
}

fn create_tok_acc_prog(svm: &mut LiteSVM, tok_prog: Address, mint: &Address, owner: &Address, amount: u64) -> Address {
    let addr = Keypair::new().pubkey();
    svm.set_account(
        addr,
        Account {
            lamports: 10_000_000,
            data: make_spl_token_account(mint, owner, amount),
            owner: tok_prog,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();
    addr
}

fn create_tok_acc(svm: &mut LiteSVM, mint: &Address, owner: &Address, amount: u64) -> Address {
    create_tok_acc_prog(svm, TOKEN_PROGRAM_ID, mint, owner, amount)
}

fn create_wsol_acc(svm: &mut LiteSVM, owner: &Address, amount: u64) -> Address {
    let addr = Keypair::new().pubkey();
    let mut data = make_spl_token_account(&WSOL_MINT, owner, amount);
    // SPL Token Account layout: is_native = COption::Some(SPL_TOKEN_RENT_MIN) at bytes 109..121
    data[109..113].copy_from_slice(&1u32.to_le_bytes());
    data[113..121].copy_from_slice(&SPL_TOKEN_RENT_MIN.to_le_bytes());
    svm.set_account(
        addr,
        Account {
            lamports: SPL_TOKEN_RENT_MIN + amount,
            data,
            owner: TOKEN_PROGRAM_ID,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();
    addr
}

fn mint_supply(svm: &LiteSVM, mint: &Address) -> u64 {
    read_u64(svm, mint, 36)
}

fn derive_rew_auth(rew_prog: &Address, cfg: &Address) -> (Address, u8) {
    Address::find_program_address(&[b"rewm", cfg.as_ref()], rew_prog)
}

/// Pure PDA derivation ONLY — does NOT mock or create the account!
/// `InitDex` itself creates & initializes the SPL Token vault account on-chain via CPI!
fn derive_dex_vault(prog_id: &Address, dex: &Address) -> (Address, u8) {
    Address::find_program_address(&[b"dvlt", dex.as_ref()], prog_id)
}

/// Global + per-market + per-portfolio EXACT invariant verifier!
fn assert_dex_invariants(
    svm: &LiteSVM,
    dex: &Address,
    dex_vault: &Address,
    markets: &[Address],
    portfolios: &[Address],
    label: &str,
) {
    let v = read_u64(svm, dex, 160);
    let c_tot = read_u64(svm, dex, 168);
    let i_tot = read_u64(svm, dex, 176);
    let r_tot = read_u64(svm, dex, 184);
    let s_tot = read_u64(svm, dex, 192);
    let f_tot = read_u64(svm, dex, 200);
    let spl = token_amount(svm, dex_vault);

    assert_eq!(v, spl, "[{}] Dex.vaultBalance ({}) != SPL balance ({})", label, v, spl);
    assert_eq!(
        c_tot as u128 + i_tot as u128 + r_tot as u128 + s_tot as u128 + f_tot as u128,
        v as u128,
        "[{}] EXACT 5-bucket stock equality violated: C({}) + I({}) + R({}) + S({}) + F({}) != V({})",
        label, c_tot, i_tot, r_tot, s_tot, f_tot, v
    );

    let mut sum_i: u64 = 0;
    let mut sum_r: u64 = 0;
    let mut sum_f: u64 = 0;
    for m in markets {
        let r_m = read_u64(svm, m, 216);
        let i_m = read_u64(svm, m, 224);
        let f_m = read_u64(svm, m, 360);
        let oi_l = read_u64(svm, m, 256);
        let oi_s = read_u64(svm, m, 264);
        let raw_l = read_u64(svm, m, 272);
        let raw_s = read_u64(svm, m, 280);
        let adl_l = read_u64(svm, m, 288);
        let adl_s = read_u64(svm, m, 296);
        let max_oi = read_u64(svm, m, 208);

        assert_eq!(oi_l, oi_s, "[{}] Market OI imbalanced: {} != {}", label, oi_l, oi_s);
        assert!(oi_l <= max_oi, "[{}] Market OI {} > maxOi {}", label, oi_l, max_oi);
        assert!(oi_l <= raw_l, "[{}] oiLong {} > rawBasisLong {}", label, oi_l, raw_l);
        assert!(oi_s <= raw_s, "[{}] oiShort {} > rawBasisShort {}", label, oi_s, raw_s);
        assert!(adl_l <= ADL_ONE, "[{}] adlLong {} > ADL_ONE", label, adl_l);
        assert!(adl_s <= ADL_ONE, "[{}] adlShort {} > ADL_ONE", label, adl_s);
        sum_i += i_m;
        sum_r += r_m;
        sum_f += f_m;
    }
    assert_eq!(sum_i, i_tot, "[{}] Σ m.insurance ({}) != Dex.totalInsurance ({})", label, sum_i, i_tot);
    assert_eq!(sum_r, r_tot, "[{}] Σ m.realizedPool ({}) != Dex.totalResidual ({})", label, sum_r, r_tot);
    assert_eq!(sum_f, f_tot, "[{}] Σ m.rewardAccrued ({}) != Dex.totalRewards ({})", label, sum_f, f_tot);
    let _ = s_tot;

    let mut sum_c: u64 = 0;
    for p in portfolios {
        let free_cap = read_u64(svm, p, 88);
        let tot_locked = read_u64(svm, p, 16);
        let tot_mm = read_u64(svm, p, 96);
        let tot_im = read_u64(svm, p, 104);
        let leg_cnt = read_u8(svm, p, 4);
        assert!(leg_cnt as usize <= MAX_LEGS, "[{}] Portfolio legCount exceeded MAX_LEGS: {}", label, leg_cnt);
        let mut calc_mm: u64 = 0;
        let mut calc_im: u64 = 0;
        let mut calc_locked: u64 = 0;
        let mut calc_cnt: u8 = 0;
        for idx in 0..MAX_LEGS {
            let base = LEG_HEADER + idx * LEG_STRIDE;
            let l_locked = read_u64(svm, p, base + 96);
            if read_u8(svm, p, base) != 0 {
                let l_mm = read_u64(svm, p, base + 72);
                let l_im = read_u64(svm, p, base + 80);
                calc_cnt += 1;
                calc_mm += l_mm;
                calc_im += l_im;
                calc_locked += l_locked;
            } else {
                assert_eq!(l_locked, 0, "[{}] Inactive leg {} has nonzero lockedMm {}", label, idx, l_locked);
            }
        }
        assert_eq!(calc_mm, tot_mm, "[{}] Portfolio totalMm mismatch: calc {} != stored {}", label, calc_mm, tot_mm);
        assert_eq!(calc_im, tot_im, "[{}] Portfolio totalIm mismatch: calc {} != stored {}", label, calc_im, tot_im);
        assert_eq!(calc_locked, tot_locked, "[{}] Portfolio totalLockedMm mismatch: calc {} != stored {}", label, calc_locked, tot_locked);
        assert_eq!(calc_cnt, leg_cnt, "[{}] Portfolio legCount mismatch: calc {} != stored {}", label, calc_cnt, leg_cnt);
        sum_c += free_cap + tot_locked;
    }
    assert_eq!(sum_c, c_tot, "[{}] Σ (pfl.freeCapital + pfl.totalLockedMm) ({}) != Dex.totalCapital ({})", label, sum_c, c_tot);
}

// ============================================================================
// Instruction Builders (19 Unified v2 Instructions)
// ============================================================================

fn ix_init_dex(
    prog: Address, dex: Address, admin: Address, mint: Address,
    vault_pda: Address, fee_vault: Address, tok_prog: Address, sys_prog: Address,
    bump: u8, decimals: u8, create_fee: u64, rent_lamports: u64,
) -> Instruction {
    let mut data = vec![0u8; 20];
    data[0] = 0;
    data[1] = bump;
    data[2] = decimals;
    data[4..12].copy_from_slice(&create_fee.to_le_bytes());
    data[12..20].copy_from_slice(&rent_lamports.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(admin, true),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(fee_vault, false),
            AccountMeta::new_readonly(tok_prog, false),
            AccountMeta::new_readonly(sys_prog, false),
        ],
        data,
    }
}

fn ix_sweep_surplus(
    prog: Address, dex: Address, admin: Address, mint: Address,
    vault_pda: Address, fee_vault: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 20;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new_readonly(admin, true),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new(fee_vault, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_update_create_fee(prog: Address, dex: Address, admin: Address, new_fee: u64, new_admin: Option<Address>) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 1;
    data[1..9].copy_from_slice(&new_fee.to_le_bytes());
    let mut accounts = vec![AccountMeta::new(dex, false), AccountMeta::new_readonly(admin, true)];
    if let Some(na) = new_admin {
        accounts.push(AccountMeta::new_readonly(na, false));
    }
    Instruction { program_id: prog, accounts, data }
}

#[allow(clippy::too_many_arguments)]
fn ix_create_market_ext(
    prog: Address, dex: Address, mkt: Address, mint: Address, oracle_auth: Address,
    creator: Address, creator_tok: Address, fee_vault: Address,
    init_price: u64, exit_window: u64, max_staleness: u64, warmup_slots: u64,
    im_bps: u64, mm_bps: u64, liq_fee_bps: u64, trade_fee_bps: u64,
    max_move_bps: u64, max_ins_draw_bps: u64, max_oi: u64, min_mm: u64,
) -> Instruction {
    let mut data = vec![0u8; 100];
    data[0] = 2;
    data[4..12].copy_from_slice(&init_price.to_le_bytes());
    data[12..20].copy_from_slice(&exit_window.to_le_bytes());
    data[20..28].copy_from_slice(&max_staleness.to_le_bytes());
    data[28..36].copy_from_slice(&warmup_slots.to_le_bytes());
    data[36..44].copy_from_slice(&im_bps.to_le_bytes());
    data[44..52].copy_from_slice(&mm_bps.to_le_bytes());
    data[52..60].copy_from_slice(&liq_fee_bps.to_le_bytes());
    data[60..68].copy_from_slice(&trade_fee_bps.to_le_bytes());
    data[68..76].copy_from_slice(&max_move_bps.to_le_bytes());
    data[76..84].copy_from_slice(&max_ins_draw_bps.to_le_bytes());
    data[84..92].copy_from_slice(&max_oi.to_le_bytes());
    data[92..100].copy_from_slice(&min_mm.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(oracle_auth, false),
            AccountMeta::new_readonly(creator, true),
            AccountMeta::new(creator_tok, false),
            AccountMeta::new(fee_vault, false),
            AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_create_market(
    prog: Address, dex: Address, mkt: Address, mint: Address, oracle_auth: Address,
    creator: Address, creator_tok: Address, fee_vault: Address,
    init_price: u64, exit_window: u64, max_staleness: u64, warmup_slots: u64,
    im_bps: u64, mm_bps: u64, liq_fee_bps: u64, trade_fee_bps: u64,
    max_move_bps: u64, max_ins_draw_bps: u64, max_oi: u64,
) -> Instruction {
    ix_create_market_ext(prog, dex, mkt, mint, oracle_auth, creator, creator_tok, fee_vault,
        init_price, exit_window, max_staleness, warmup_slots, im_bps, mm_bps, liq_fee_bps,
        trade_fee_bps, max_move_bps, max_ins_draw_bps, max_oi, 0)
}

#[allow(clippy::too_many_arguments)]
fn ix_create_market_with_reward(
    prog: Address, dex: Address, mkt: Address, mint: Address, oracle_auth: Address,
    creator: Address, creator_tok: Address, fee_vault: Address,
    init_price: u64, exit_window: u64, max_staleness: u64, warmup_slots: u64,
    im_bps: u64, mm_bps: u64, liq_fee_bps: u64, trade_fee_bps: u64,
    max_move_bps: u64, max_ins_draw_bps: u64, max_oi: u64, min_mm: u64,
    reward_bps: u64, reward_recipient: Address,
) -> Instruction {
    let mut ix = ix_create_market_ext(
        prog, dex, mkt, mint, oracle_auth, creator, creator_tok, fee_vault,
        init_price, exit_window, max_staleness, warmup_slots,
        im_bps, mm_bps, liq_fee_bps, trade_fee_bps,
        max_move_bps, max_ins_draw_bps, max_oi, min_mm,
    );
    ix.data.resize(140, 0);
    ix.data[100..108].copy_from_slice(&reward_bps.to_le_bytes());
    ix.data[108..140].copy_from_slice(reward_recipient.as_ref());
    ix
}

fn ix_claim_reward(
    prog: Address, dex: Address, mkt: Address, rew_auth: Address,
    mint: Address, vault_pda: Address, dest_tok: Address, tok_prog: Address, req_amt: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 21;
    data[1..9].copy_from_slice(&req_amt.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(rew_auth, true),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new(dest_tok, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_set_portfolio_matcher(
    prog: Address, pfl: Address, owner: Address, matcher_ctx: Option<Address>,
) -> Instruction {
    let mut accounts = vec![
        AccountMeta::new(pfl, false),
        AccountMeta::new_readonly(owner, true),
    ];
    if let Some(mc) = matcher_ctx {
        accounts.push(AccountMeta::new_readonly(mc, false));
    }
    Instruction { program_id: prog, accounts, data: vec![22] }
}

#[allow(clippy::too_many_arguments)]
fn ix_trade_with_matcher_batch(
    prog: Address, dex: Address,
    taker_pfl: Address, taker_owner: Address, lp_pfl: Address,
    matcher_prog: Address, matcher_ctx: Address,
    offers: &[(Address, u8, bool, u64, u64)], // (mkt, mode, taker_is_long, max_qty, limit_price)
    extra_acc: Option<Address>,
) -> Instruction {
    let k = offers.len();
    let mut data = vec![0u8; 2 + k * 18];
    data[0] = 23;
    data[1] = k as u8;
    let mut accounts = vec![
        AccountMeta::new(dex, false),
        AccountMeta::new(taker_pfl, false),
        AccountMeta::new_readonly(taker_owner, true),
        AccountMeta::new(lp_pfl, false),
        AccountMeta::new_readonly(matcher_prog, false),
        AccountMeta::new(matcher_ctx, false),
    ];
    for (i, &(mkt, mode, taker_is_long, max_qty, limit_price)) in offers.iter().enumerate() {
        let off = 2 + i * 18;
        data[off] = mode;
        data[off + 1] = if taker_is_long { 1 } else { 0 };
        data[off + 2..off + 10].copy_from_slice(&max_qty.to_le_bytes());
        data[off + 10..off + 18].copy_from_slice(&limit_price.to_le_bytes());
        accounts.push(AccountMeta::new(mkt, false));
    }
    if let Some(ex) = extra_acc {
        accounts.push(AccountMeta::new_readonly(ex, false));
    }
    Instruction { program_id: prog, accounts, data }
}

#[allow(clippy::too_many_arguments)]
fn ix_trade_with_matcher(
    prog: Address, dex: Address, mkt: Address,
    taker_pfl: Address, taker_owner: Address, lp_pfl: Address,
    matcher_prog: Address, matcher_ctx: Address, extra_acc: Option<Address>,
    mode: u8, taker_is_long: bool, max_qty: u64, limit_price: u64,
) -> Instruction {
    ix_trade_with_matcher_batch(
        prog, dex, taker_pfl, taker_owner, lp_pfl, matcher_prog, matcher_ctx,
        &[(mkt, mode, taker_is_long, max_qty, limit_price)], extra_acc,
    )
}

fn ix_init_prop_amm(
    matcher_prog: Address, ctx: Address, owner: Address,
    paused: u8, half_spread_bps: u64, impact_bps: u64, max_fill_qty: u64,
    allowed_markets: &[u64],
) -> Instruction {
    assert!(!allowed_markets.is_empty() && allowed_markets.len() <= MAX_LEGS);
    let mut data = vec![0u8; 28 + allowed_markets.len() * 8];
    data[0] = 0;
    data[1] = paused;
    data[2] = allowed_markets.len() as u8;
    data[4..12].copy_from_slice(&half_spread_bps.to_le_bytes());
    data[12..20].copy_from_slice(&impact_bps.to_le_bytes());
    data[20..28].copy_from_slice(&max_fill_qty.to_le_bytes());
    for (i, &mid) in allowed_markets.iter().enumerate() {
        let off = 28 + i * 8;
        data[off..off + 8].copy_from_slice(&mid.to_le_bytes());
    }
    Instruction {
        program_id: matcher_prog,
        accounts: vec![
            AccountMeta::new(ctx, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data,
    }
}

fn ix_update_prop_amm(
    matcher_prog: Address, ctx: Address, owner: Address,
    paused: u8, half_spread_bps: u64, impact_bps: u64, max_fill_qty: u64,
) -> Instruction {
    let mut data = vec![0u8; 28];
    data[0] = 1;
    data[1] = paused;
    data[4..12].copy_from_slice(&half_spread_bps.to_le_bytes());
    data[12..20].copy_from_slice(&impact_bps.to_le_bytes());
    data[20..28].copy_from_slice(&max_fill_qty.to_le_bytes());
    Instruction {
        program_id: matcher_prog,
        accounts: vec![
            AccountMeta::new(ctx, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_init_hlp_vault(
    hlp_prog: Address, vault: Address, strategist: Address, dex: Address,
    hlp_pfl: Address, hlp_auth_pda: Address, hlp_fee_tok: Address, perc_prog: Address,
    allowed_matcher_prog: Address,
    bump: u8, lockup_slots: u64, deposit_cap: u64, min_deposit: u64,
    allowed_markets: &[u64],
) -> Instruction {
    assert!(!allowed_markets.is_empty() && allowed_markets.len() <= MAX_LEGS);
    let mut data = vec![0u8; 28 + allowed_markets.len() * 8];
    data[0] = 0;
    data[1] = bump;
    data[2] = allowed_markets.len() as u8;
    data[4..12].copy_from_slice(&lockup_slots.to_le_bytes());
    data[12..20].copy_from_slice(&deposit_cap.to_le_bytes());
    data[20..28].copy_from_slice(&min_deposit.to_le_bytes());
    for (i, &mid) in allowed_markets.iter().enumerate() {
        let off = 28 + i * 8;
        data[off..off + 8].copy_from_slice(&mid.to_le_bytes());
    }
    Instruction {
        program_id: hlp_prog,
        accounts: vec![
            AccountMeta::new(vault, false),
            AccountMeta::new_readonly(strategist, true),
            AccountMeta::new(dex, false),
            AccountMeta::new(hlp_pfl, false),
            AccountMeta::new_readonly(hlp_auth_pda, false),
            AccountMeta::new_readonly(hlp_fee_tok, false),
            AccountMeta::new_readonly(perc_prog, false),
            AccountMeta::new_readonly(allowed_matcher_prog, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_set_hlp_matcher(
    hlp_prog: Address, vault: Address, strategist: Address,
    hlp_pfl: Address, hlp_auth_pda: Address, perc_prog: Address,
    matcher_ctx: Option<Address>, paused: Option<u8>,
) -> Instruction {
    let mut data = vec![1u8];
    if let Some(p) = paused { data.push(p); }
    let mut accounts = vec![
        AccountMeta::new(vault, false),
        AccountMeta::new_readonly(strategist, true),
        AccountMeta::new(hlp_pfl, false),
        AccountMeta::new_readonly(hlp_auth_pda, false),
        AccountMeta::new_readonly(perc_prog, false),
    ];
    if let Some(mc) = matcher_ctx {
        accounts.push(AccountMeta::new_readonly(mc, false));
    }
    Instruction { program_id: hlp_prog, accounts, data }
}

#[allow(clippy::too_many_arguments)]
fn ix_deposit_hlp(
    hlp_prog: Address, vault: Address, receipt: Address, depositor: Address,
    depositor_tok: Address, dex: Address, hlp_pfl: Address, mint: Address,
    dex_vault: Address, tok_prog: Address, perc_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 2;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: hlp_prog,
        accounts: vec![
            AccountMeta::new(vault, false),
            AccountMeta::new(receipt, false),
            AccountMeta::new_readonly(depositor, true),
            AccountMeta::new(depositor_tok, false),
            AccountMeta::new(dex, false),
            AccountMeta::new(hlp_pfl, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(dex_vault, false),
            AccountMeta::new_readonly(tok_prog, false),
            AccountMeta::new_readonly(perc_prog, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_withdraw_hlp(
    hlp_prog: Address, vault: Address, receipt: Address, owner: Address,
    dest_tok: Address, dex: Address, hlp_pfl: Address, hlp_auth_pda: Address,
    mint: Address, dex_vault: Address, tok_prog: Address, perc_prog: Address, burn_shares: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 3;
    data[1..9].copy_from_slice(&burn_shares.to_le_bytes());
    Instruction {
        program_id: hlp_prog,
        accounts: vec![
            AccountMeta::new(vault, false),
            AccountMeta::new(receipt, false),
            AccountMeta::new(owner, true),
            AccountMeta::new(dest_tok, false),
            AccountMeta::new(dex, false),
            AccountMeta::new(hlp_pfl, false),
            AccountMeta::new_readonly(hlp_auth_pda, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(dex_vault, false),
            AccountMeta::new_readonly(tok_prog, false),
            AccountMeta::new_readonly(perc_prog, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_hlp_takeover_liquidate(
    hlp_prog: Address, vault: Address, strategist: Address, dex: Address,
    mkt: Address, victim_pfl: Address, hlp_fee_tok: Address, mint: Address,
    dex_vault: Address, tok_prog: Address, hlp_pfl: Address, hlp_auth_pda: Address,
    perc_prog: Address, req_qty: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 4;
    data[1..9].copy_from_slice(&req_qty.to_le_bytes());
    Instruction {
        program_id: hlp_prog,
        accounts: vec![
            AccountMeta::new_readonly(vault, false),
            AccountMeta::new_readonly(strategist, true),
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(victim_pfl, false),
            AccountMeta::new(hlp_fee_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(dex_vault, false),
            AccountMeta::new_readonly(tok_prog, false),
            AccountMeta::new(hlp_pfl, false),
            AccountMeta::new_readonly(hlp_auth_pda, false),
            AccountMeta::new_readonly(perc_prog, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_init_reward(
    rew_prog: Address, cfg: Address, mkt_admin: Address, perc_prog: Address,
    dex: Address, mkt: Address, rew_auth_pda: Address,
    quote_mint: Address, quote_vault: Address, quote_tok_prog: Address,
    target_mint: Address, target_escrow: Address, target_tok_prog: Address,
    burn_sink_tok: Option<Address>,
    bump: u8, burn_mode: u8, epoch_slots: u64, min_batch_quote: u64, init_reserve_rate_e6: u64,
) -> Instruction {
    let mut data = vec![0u8; 28];
    data[0] = 0;
    data[1] = bump;
    data[2] = burn_mode;
    data[4..12].copy_from_slice(&epoch_slots.to_le_bytes());
    data[12..20].copy_from_slice(&min_batch_quote.to_le_bytes());
    data[20..28].copy_from_slice(&init_reserve_rate_e6.to_le_bytes());
    let mut accounts = vec![
        AccountMeta::new(cfg, false),
        AccountMeta::new_readonly(mkt_admin, true),
        AccountMeta::new_readonly(perc_prog, false),
        AccountMeta::new_readonly(dex, false),
        AccountMeta::new_readonly(mkt, false),
        AccountMeta::new_readonly(rew_auth_pda, false),
        AccountMeta::new_readonly(quote_mint, false),
        AccountMeta::new_readonly(quote_vault, false),
        AccountMeta::new_readonly(quote_tok_prog, false),
        AccountMeta::new_readonly(target_mint, false),
        AccountMeta::new_readonly(target_escrow, false),
        AccountMeta::new_readonly(target_tok_prog, false),
    ];
    if let Some(sink) = burn_sink_tok {
        accounts.push(AccountMeta::new_readonly(sink, false));
    }
    Instruction { program_id: rew_prog, accounts, data }
}

#[allow(clippy::too_many_arguments)]
fn ix_start_epoch(
    rew_prog: Address, cfg: Address, epoch_acc: Address, dex: Address, mkt: Address,
    rew_auth_pda: Address, quote_mint: Address, dex_vault: Address, quote_vault: Address,
    quote_tok_prog: Address, perc_prog: Address,
) -> Instruction {
    Instruction {
        program_id: rew_prog,
        accounts: vec![
            AccountMeta::new(cfg, false),
            AccountMeta::new(epoch_acc, false),
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(rew_auth_pda, false),
            AccountMeta::new_readonly(quote_mint, false),
            AccountMeta::new(dex_vault, false),
            AccountMeta::new(quote_vault, false),
            AccountMeta::new_readonly(quote_tok_prog, false),
            AccountMeta::new_readonly(perc_prog, false),
        ],
        data: vec![1],
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_submit_bid(
    rew_prog: Address, cfg: Address, epoch_acc: Address, bid_receipt: Address,
    bidder: Address, bidder_target_tok: Address, target_escrow: Address,
    target_mint: Address, target_tok_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 2;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: rew_prog,
        accounts: vec![
            AccountMeta::new_readonly(cfg, false),
            AccountMeta::new(epoch_acc, false),
            AccountMeta::new(bid_receipt, false),
            AccountMeta::new_readonly(bidder, true),
            AccountMeta::new(bidder_target_tok, false),
            AccountMeta::new(target_escrow, false),
            AccountMeta::new_readonly(target_mint, false),
            AccountMeta::new_readonly(target_tok_prog, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_settle_epoch(
    rew_prog: Address, cfg: Address, epoch_acc: Address, rew_auth_pda: Address,
    target_escrow: Address, target_mint: Address, target_tok_prog: Address,
    burn_sink_tok: Option<Address>,
) -> Instruction {
    let mut accounts = vec![
        AccountMeta::new(cfg, false),
        AccountMeta::new(epoch_acc, false),
        AccountMeta::new_readonly(rew_auth_pda, false),
        AccountMeta::new(target_escrow, false),
        AccountMeta::new(target_mint, false),
        AccountMeta::new_readonly(target_tok_prog, false),
    ];
    if let Some(sink) = burn_sink_tok {
        accounts.push(AccountMeta::new(sink, false));
    }
    Instruction { program_id: rew_prog, accounts, data: vec![3] }
}

#[allow(clippy::too_many_arguments)]
fn ix_claim_quote(
    rew_prog: Address, cfg: Address, epoch_acc: Address, bid_receipt: Address,
    bidder: Address, rew_auth_pda: Address, quote_vault: Address,
    bidder_quote_tok: Address, quote_mint: Address, quote_tok_prog: Address,
) -> Instruction {
    Instruction {
        program_id: rew_prog,
        accounts: vec![
            AccountMeta::new(cfg, false),
            AccountMeta::new(epoch_acc, false),
            AccountMeta::new(bid_receipt, false),
            AccountMeta::new(bidder, true),
            AccountMeta::new_readonly(rew_auth_pda, false),
            AccountMeta::new(quote_vault, false),
            AccountMeta::new(bidder_quote_tok, false),
            AccountMeta::new_readonly(quote_mint, false),
            AccountMeta::new_readonly(quote_tok_prog, false),
        ],
        data: vec![4],
    }
}

fn ix_burn_market_admin(prog: Address, mkt: Address, admin: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(admin, true)],
        data: vec![3, 0],
    }
}

fn ix_update_market_auth(prog: Address, mkt: Address, admin: Address, role: u8, new_key: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(admin, true),
            AccountMeta::new_readonly(new_key, false),
        ],
        data: vec![3, role],
    }
}

fn ix_close_account(prog: Address, acc: Address, authority: Address, dest: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(acc, false),
            AccountMeta::new_readonly(authority, true),
            AccountMeta::new(dest, false),
        ],
        data: vec![19],
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_liquidate_ext(
    prog: Address, dex: Address, mkt: Address, pfl: Address,
    liq_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address,
    mode: u8, req_qty: u64, takeover: Option<(Address, Address)>,
) -> Instruction {
    let mut data = vec![0u8; 10];
    data[0] = 12;
    data[1] = mode;
    data[2..10].copy_from_slice(&req_qty.to_le_bytes());
    let mut accounts = vec![
        AccountMeta::new(dex, false),
        AccountMeta::new(mkt, false),
        AccountMeta::new(pfl, false),
        AccountMeta::new(liq_tok, false),
        AccountMeta::new_readonly(mint, false),
        AccountMeta::new(vault_pda, false),
        AccountMeta::new_readonly(tok_prog, false),
    ];
    if let Some((liq_pfl, liq_owner)) = takeover {
        accounts.push(AccountMeta::new(liq_pfl, false));
        accounts.push(AccountMeta::new_readonly(liq_owner, true));
    }
    Instruction { program_id: prog, accounts, data }
}

fn ix_update_oracle(prog: Address, mkt: Address, oracle_auth: Address, new_price: u64, fund_sign: u8, fund_e6: u64) -> Instruction {
    let mut data = vec![0u8; 18];
    data[0] = 4;
    data[1..9].copy_from_slice(&new_price.to_le_bytes());
    data[9] = fund_sign;
    data[10..18].copy_from_slice(&fund_e6.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(oracle_auth, true)],
        data,
    }
}

/// Smoothly step `mkt` oracle to `target_price` respecting the K=4 per-slot clamp (`maxMoveBps`),
/// advancing the LiteSVM slot by 1 per step. Returns the last step's CU.
fn step_oracle(
    svm: &mut LiteSVM, prog: Address, mkt: Address, oracle: &Keypair,
    target_price: u64, payer: &Keypair,
) -> u64 {
    let max_move_bps = read_u64(svm, &mkt, 192);
    let mut cur = read_u64(svm, &mkt, 112);
    let mut last_cu = 0u64;
    let mut guard = 0u32;
    while cur != target_price {
        guard += 1;
        assert!(guard < 400, "step_oracle did not converge: cur={} target={}", cur, target_price);
        let next_slot = get_slot(svm) + 1;
        set_slot(svm, next_slot);
        let max_step = (((cur as u128 * max_move_bps as u128) / 10_000) as u64).max(1);
        let next_p = if target_price > cur {
            cur.saturating_add(max_step).min(target_price)
        } else {
            cur.saturating_sub(max_step).max(target_price)
        };
        last_cu = send_ok(svm, ix_update_oracle(prog, mkt, oracle.pubkey(), next_p, 0, 0), payer, &[payer, oracle]);
        cur = next_p;
    }
    last_cu
}

/// Synchronously step TWO markets' oracles in lockstep to `target_price` (1 slot per step).
fn step_two_oracles(
    svm: &mut LiteSVM, prog: Address, mkt1: Address, orc1: &Keypair,
    mkt2: Address, orc2: &Keypair, target_price: u64, payer: &Keypair,
) -> u64 {
    let bps1 = read_u64(svm, &mkt1, 192);
    let bps2 = read_u64(svm, &mkt2, 192);
    let mut c1 = read_u64(svm, &mkt1, 112);
    let mut c2 = read_u64(svm, &mkt2, 112);
    let mut last_cu = 0u64;
    let mut guard = 0u32;
    while c1 != target_price || c2 != target_price {
        guard += 1;
        assert!(guard < 400, "step_two_oracles did not converge");
        let next_slot = get_slot(svm) + 1;
        set_slot(svm, next_slot);
        if c1 != target_price {
            let ms = (((c1 as u128 * bps1 as u128) / 10_000) as u64).max(1);
            c1 = if target_price > c1 { c1.saturating_add(ms).min(target_price) } else { c1.saturating_sub(ms).max(target_price) };
            last_cu = send_ok(svm, ix_update_oracle(prog, mkt1, orc1.pubkey(), c1, 0, 0), payer, &[payer, orc1]);
        }
        if c2 != target_price {
            let ms = (((c2 as u128 * bps2 as u128) / 10_000) as u64).max(1);
            c2 = if target_price > c2 { c2.saturating_add(ms).min(target_price) } else { c2.saturating_sub(ms).max(target_price) };
            send_ok(svm, ix_update_oracle(prog, mkt2, orc2.pubkey(), c2, 0, 0), payer, &[payer, orc2]);
        }
    }
    last_cu
}

fn ix_init_portfolio(prog: Address, dex: Address, pfl: Address, owner: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: vec![5],
    }
}

fn ix_deposit_collateral(
    prog: Address, dex: Address, pfl: Address, owner: Address,
    owner_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 6;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
            AccountMeta::new(owner_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_withdraw_collateral(
    prog: Address, dex: Address, pfl: Address, owner: Address,
    dest_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 7;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
            AccountMeta::new(dest_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_deposit_insurance_ext(
    prog: Address, dex: Address, mkt: Address, receipt: Address, lp: Address,
    lp_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64, donate: bool,
) -> Instruction {
    let mut data = vec![0u8; 10];
    data[0] = 8;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    data[9] = if donate { 1 } else { 0 };
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(receipt, false),
            AccountMeta::new_readonly(lp, true),
            AccountMeta::new(lp_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_deposit_insurance(
    prog: Address, dex: Address, mkt: Address, receipt: Address, lp: Address,
    lp_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    ix_deposit_insurance_ext(prog, dex, mkt, receipt, lp, lp_tok, mint, vault_pda, tok_prog, amount, false)
}

fn ix_withdraw_insurance(
    prog: Address, dex: Address, mkt: Address, receipt: Address, lp: Address,
    dest_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, burn_shares: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 9;
    data[1..9].copy_from_slice(&burn_shares.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(receipt, false),
            AccountMeta::new_readonly(lp, true),
            AccountMeta::new(dest_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_refresh_leg(prog: Address, dex: Address, mkt: Address, pfl: Address, force_haircut: bool) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
        ],
        data: vec![10, if force_haircut { 1 } else { 0 }],
    }
}

fn ix_refresh_leg_signed(
    prog: Address, dex: Address, mkt: Address, pfl: Address, owner: Address, force_haircut: bool,
) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: vec![10, if force_haircut { 1 } else { 0 }],
    }
}

fn ix_trade_ext(
    prog: Address, dex: Address, mkt: Address,
    pfl_l: Address, owner_l: Address, pfl_s: Address, owner_s: Address,
    mode: u8, qty: u64, exec_price: u64,
) -> Instruction {
    let mut data = vec![0u8; 18];
    data[0] = 11;
    data[1] = mode;
    data[2..10].copy_from_slice(&qty.to_le_bytes());
    data[10..18].copy_from_slice(&exec_price.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl_l, false),
            AccountMeta::new_readonly(owner_l, true),
            AccountMeta::new(pfl_s, false),
            AccountMeta::new_readonly(owner_s, true),
        ],
        data,
    }
}

fn ix_trade(
    prog: Address, dex: Address, mkt: Address,
    pfl_l: Address, owner_l: Address, pfl_s: Address, owner_s: Address,
    mode: u8, qty: u64,
) -> Instruction {
    ix_trade_ext(prog, dex, mkt, pfl_l, owner_l, pfl_s, owner_s, mode, qty, 0)
}

fn ix_liquidate(
    prog: Address, dex: Address, mkt: Address, pfl: Address,
    liq_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address,
) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new(liq_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data: vec![12],
    }
}

fn ix_clear_dead_leg(prog: Address, dex: Address, mkt: Address, pfl: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
        ],
        data: vec![13],
    }
}

fn ix_start_wind_down(prog: Address, mkt: Address, caller: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(caller, true)],
        data: vec![14],
    }
}

fn ix_force_close_pair(prog: Address, dex: Address, mkt: Address, pfl_l: Address, pfl_s: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl_l, false),
            AccountMeta::new(pfl_s, false),
        ],
        data: vec![15],
    }
}

fn ix_resolve_market(prog: Address, dex: Address, mkt: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(dex, false), AccountMeta::new(mkt, false)],
        data: vec![16],
    }
}

fn ix_claim_resolved(prog: Address, dex: Address, mkt: Address, pfl: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
        ],
        data: vec![17],
    }
}

fn ix_tombstone_market(prog: Address, mkt: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false)],
        data: vec![18],
    }
}

/// Build `RefreshLeg` instructions for every active open leg of `pfl` in `markets_by_id`.
fn refresh_open_legs_ixs(
    svm: &LiteSVM,
    prog: Address,
    dex: Address,
    pfl: Address,
    markets: &[(u64, Address)],
) -> Vec<Instruction> {
    let mut ixs = Vec::new();
    for idx in 0..MAX_LEGS {
        let base = LEG_HEADER + idx * LEG_STRIDE;
        if read_u8(svm, &pfl, base) != 0 && read_u8(svm, &pfl, base + 1) != 0 {
            let mid = read_u64(svm, &pfl, base + 8);
            if let Some((_, mkt)) = markets.iter().find(|(id, _)| *id == mid) {
                ixs.push(ix_refresh_leg(prog, dex, *mkt, pfl, false));
            }
        }
    }
    ixs
}

/// Deterministic xorshift64 PRNG for reproducible 1,000-step stateful fuzzing.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn range(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
}

/// Enforce strict shipping sBPF v3 ELF64 header invariants (SIMD-0178 + SIMD-0189 + SIMD-0377 + SIMD-0500):
/// `e_machine == EM_BPF (247)`, `e_entry == 0x100000000`, `e_flags == 3 (SBPFVersion::V3)`,
/// `e_phnum ∈ 1..=2`, and every PHDR is `PT_LOAD (1)` (zero `PT_DYNAMIC`, zero relocations).
fn assert_sbpf_v3_elf(name: &str, elf: &[u8]) {
    assert!(elf.len() >= 64, "{name}: ELF truncated (< 64 bytes)");
    assert_eq!(&elf[0..4], b"\x7fELF", "{name}: bad ELF magic");
    assert_eq!(elf[4], 2, "{name}: must be ELFCLASS64");
    assert_eq!(elf[5], 1, "{name}: must be ELFDATA2LSB");
    assert_eq!(u16::from_le_bytes(elf[16..18].try_into().unwrap()), 3, "{name}: must be ET_DYN");
    assert_eq!(u16::from_le_bytes(elf[18..20].try_into().unwrap()), 247, "{name}: must be EM_BPF (247)");
    assert_eq!(u64::from_le_bytes(elf[24..32].try_into().unwrap()), 0x1_0000_0000, "{name}: e_entry must be MM_BYTECODE_START (0x100000000)");
    assert_eq!(u64::from_le_bytes(elf[32..40].try_into().unwrap()), 64, "{name}: e_phoff must be 64");
    assert_eq!(u32::from_le_bytes(elf[48..52].try_into().unwrap()), 3, "{name}: e_flags must be 3 (SBPFVersion::V3 / SIMD-0500)");
    let phnum = u16::from_le_bytes(elf[56..58].try_into().unwrap()) as usize;
    assert!((1..=2).contains(&phnum), "{name}: strict sBPF v3 must have 1 or 2 PHDRs, got {phnum}");
    for i in 0..phnum {
        let off = 64 + i * 56;
        let p_type = u32::from_le_bytes(elf[off..off + 4].try_into().unwrap());
        assert_eq!(p_type, 1, "{name}: PHDR[{i}] must be PT_LOAD (1), got {p_type} (no PT_DYNAMIC allowed)");
    }
}

fn main() {
    let so_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "build/percolator.so".to_string());
    let elf = std::fs::read(&so_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", so_path, e));
    assert_sbpf_v3_elf(&so_path, &elf);
    for arg in std::env::args().skip(2) {
        let extra = std::fs::read(&arg).unwrap_or_else(|e| panic!("Failed to read {}: {}", arg, e));
        assert_sbpf_v3_elf(&arg, &extra);
    }
    println!("==================================================================================");
    println!("  percolator-lean v2 — Realizable Shared Cross-Margin Perps DEX Verification Suite");
    println!("  Binary: {} ({} bytes, sBPF v3 e_flags=3, 0 relocs, 0 heap)", so_path, elf.len());
    println!("==================================================================================");

    let mut svm = LiteSVM::new();
    let prog_id = Keypair::new().pubkey();
    svm.add_program(prog_id, &elf).expect("ELF load failed");
    set_slot(&mut svm, 100);

    let payer = Keypair::new();
    let dex_admin = Keypair::new();
    let alice = Keypair::new();
    let bob = Keypair::new();
    let lp = Keypair::new();
    let keeper = Keypair::new();
    let attacker = Keypair::new();
    let btc_oracle = Keypair::new();
    let eth_oracle = Keypair::new();
    let scam_oracle = Keypair::new();
    let adl_oracle = Keypair::new();
    let fake_tok_prog = Keypair::new().pubkey();
    // Load a REAL executable no-op sBPF program (returns Ok(0) on any CPI!) as `fake_tok_prog`!
    // If `checkDexVaultAndMint` / `checkTokenProg` error were ever dropped, DepositCollateral would
    // SUCCEED and mint phantom collateral; with the fix, every CPI entry MUST reject with Custom(120).
    let noop_elf = std::fs::read("../lean-svm/build/noop.so")
        .expect("Failed to read ../lean-svm/build/noop.so (run lean-svm build first)");
    svm.add_program(fake_tok_prog, &noop_elf).expect("noop ELF load failed");

    for kp in [&payer, &dex_admin, &alice, &bob, &lp, &keeper, &attacker, &btc_oracle, &eth_oracle, &scam_oracle, &adl_oracle] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }

    // Create USDC (6 decimals) quote mint
    let mint = Keypair::new().pubkey();
    svm.set_account(
        mint,
        Account {
            lamports: 10_000_000,
            data: make_spl_mint(6, 10_000_000_000_000, &dex_admin.pubkey()),
            owner: TOKEN_PROGRAM_ID,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();

    let fee_vault = create_tok_acc(&mut svm, &mint, &dex_admin.pubkey(), 0);
    let admin_tok = create_tok_acc(&mut svm, &mint, &dex_admin.pubkey(), 10_000_000_000);
    let alice_tok = create_tok_acc(&mut svm, &mint, &alice.pubkey(), 10_000_000_000);
    let bob_tok = create_tok_acc(&mut svm, &mint, &bob.pubkey(), 10_000_000_000);
    let lp_tok = create_tok_acc(&mut svm, &mint, &lp.pubkey(), 10_000_000_000);
    let keeper_tok = create_tok_acc(&mut svm, &mint, &keeper.pubkey(), 0);
    let attacker_tok = create_tok_acc(&mut svm, &mint, &attacker.pubkey(), 10_000_000_000);

    // =========================================================================
    // SUITE 1: Real On-Chain InitDex PDA Vault Creation (ZERO vault mocks!)
    //   Tests fake tokenProg, fake sysProg, wrong bump, AND 1-lamport pre-funding
    //   griefing resilience! `InitDex` allocates, assigns & InitializeAccount3's
    //   the real SPL Token vault PDA on-chain via CPI!
    // =========================================================================
    let dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (dex_vault, dex_bump) = derive_dex_vault(&prog_id, &dex);

    // Pre-send 1 lamport to `dex_vault` to simulate an attacker trying to grief PDA creation!
    svm.set_account(
        dex_vault,
        Account { lamports: 1, data: vec![], owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 },
    )
    .unwrap();

    // 1a. Reject fake Token Program ID
    send_err(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, fake_tok_prog, SYSTEM_PROGRAM_ID, dex_bump, 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
        "InitDex with fake tokenProg",
    );
    // 1b. Reject fake System Program ID
    send_err(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, TOKEN_PROGRAM_ID, fake_tok_prog, dex_bump, 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
        "InitDex with fake sysProg",
    );
    // 1c. Reject wrong PDA bump
    send_err(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, dex_bump.wrapping_sub(1), 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
        "InitDex with wrong PDA bump",
    );

    // 1d. InitDex creates the real SPL Token PDA vault on-chain despite 1-lamport pre-funding!
    let cu_init_dex = send_ok(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, dex_bump, 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
    );
    let vault_acc = svm.get_account(&dex_vault).expect("DexVault PDA must exist on-chain!");
    assert_eq!(vault_acc.owner, TOKEN_PROGRAM_ID);
    assert_eq!(vault_acc.data.len(), 165);
    assert_eq!(vault_acc.lamports, SPL_TOKEN_RENT_MIN);
    assert_eq!(token_amount(&svm, &dex_vault), 0);
    assert_dex_invariants(&svm, &dex, &dex_vault, &[], &[], "post-initDex");
    println!("[PASS] Suite 1: Real On-Chain InitDex PDA Vault Creation + Anti-PreFund Griefing ({} CU)", cu_init_dex);

    // =========================================================================
    // SUITE 2: Permissionless Multi-Market Creation + Solvency Envelope
    // =========================================================================
    let btc_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let eth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let scam_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let bad_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);

    // Reject invalid K+1=5 solvency envelope (`k5MoveBps + liqAtP5 <= mmBps`):
    //   1) Naive 1-slot `maxMove 500 + liqFee 100 > mmBps 500`
    //   2) Gap #1/K+1=5 catch: `maxMove 80` gives `k5(80)+liqAtP5 = 408+105 = 513 > mmBps 500` -> Custom(103)!
    send_err(
        &mut svm,
        ix_create_market(prog_id, dex, bad_mkt, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 500, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &alice],
        "CreateMarket violating solvency envelope",
    );
    send_err_custom(
        &mut svm,
        ix_create_market(prog_id, dex, bad_mkt, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 80, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &alice],
        103,
        "CreateMarket violating Gap #1 compounded K+1=5 envelope (k5(80)+liqAtP5=513 > 500)",
    );
    // Reject Gap B same-slot sandwich envelope violation (mmBps 500 + maxMove 75 = 575 > imBps 550!)
    send_err_custom(
        &mut svm,
        ix_create_market(prog_id, dex, bad_mkt, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 550, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &alice],
        103,
        "CreateMarket violating Gap B mmBps + maxMoveBps <= imBps",
    );
    // Reject Gap #2 fronting bypass (`maxFrontBps = 5000 > maxInsDrawBps = 2500` -> Custom(103)!)
    {
        let mut front_ix = ix_create_market(prog_id, dex, bad_mkt, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE);
        front_ix.data[2..4].copy_from_slice(&5000u16.to_le_bytes());
        send_err_custom(&mut svm, front_ix, &payer, &[&payer, &alice], 103,
            "CreateMarket violating Gap #2 maxFrontBps <= maxInsDrawBps");
    }

    // Truly permissionless equal markets (zero special market 0, zero admin whitelist!):
    // BTC, ETH, and attacker-created SCAM all share the DEX base collateral mint & K+1=5 clamp (maxMove=75).
    let cu_create_mkt = send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, btc_mkt, mint, btc_oracle.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &dex_admin],
    );
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, eth_mkt, mint, eth_oracle.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &dex_admin],
    );
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, scam_mkt, mint, scam_oracle.pubkey(), attacker.pubkey(), attacker_tok, fee_vault,
            100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &attacker],
    );
    assert_eq!(token_amount(&svm, &fee_vault), 3_000_000);

    // UpdateCreateFee affects ZERO markets/portfolios
    send_ok(&mut svm, ix_update_create_fee(prog_id, dex, dex_admin.pubkey(), 0, None), &payer, &[&payer, &dex_admin]);

    // Deposit isolated insurance to BTC ($1000), ETH ($500), SCAM ($100)
    let btc_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    let eth_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    let scam_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, eth_mkt, eth_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, scam_mkt, scam_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &lp]);

    let all_mkts = vec![btc_mkt, eth_mkt, scam_mkt];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &[], "post-markets");
    println!("[PASS] Suite 2: Multi-Market Creation + Solvency Envelope + Isolated Insurance ({} CU)", cu_create_mkt);

    // =========================================================================
    // SUITE 3: Hyperliquid Cross-Margin Capital Efficiency (Hedged Spread!)
    //   Alice puts up $100 shared capital, opens Long $500 BTC + Short $500 ETH
    //   (10x gross leverage, IM = $50 + $50 = $100).
    //   Both BTC & ETH drop ~7.84% over 2 slots -> atomic [RefreshLeg(ETH), RefreshLeg(BTC)]
    //   nets +$39.20 ETH profit directly against -$39.20 BTC loss -> $100 capital, 0 liquidation!
    // =========================================================================
    let alice_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let bob_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let attacker_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, alice_pfl, alice.pubkey()), &payer, &[&payer, &alice]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, bob_pfl, bob.pubkey()), &payer, &[&payer, &bob]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, attacker_pfl, attacker.pubkey()), &payer, &[&payer, &attacker]);
    let all_pfls = vec![alice_pfl, bob_pfl, attacker_pfl];

    let cu_dep = send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &alice]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &bob]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, attacker_pfl, attacker.pubkey(), attacker_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &attacker]);

    // Alice opens Long 5 BTC ($500) + Short 5 ETH ($500) on $100 capital!
    let cu_trade = send_ok(&mut svm, ix_trade(prog_id, dex, btc_mkt, alice_pfl, alice.pubkey(), bob_pfl, bob.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &alice, &bob]);
    send_ok(&mut svm, ix_trade(prog_id, dex, eth_mkt, bob_pfl, bob.pubkey(), alice_pfl, alice.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &bob, &alice]);
    assert_eq!(pfl_total_capital(&svm, &alice_pfl), 100 * POS_SCALE);
    assert_eq!(pfl_locked_mm(&svm, &alice_pfl), 50 * POS_SCALE);   // $25 BTC + $25 ETH locked MM firewall!
    assert_eq!(pfl_free_capital(&svm, &alice_pfl), 50 * POS_SCALE); // $50 free capital!
    assert_eq!(read_u64(&svm, &alice_pfl, 104), 100 * POS_SCALE); // totalIm == $100!
    assert_eq!(read_u64(&svm, &alice_pfl, 96), 50 * POS_SCALE);   // totalMm == $50!
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &all_pfls, "post-spread-open");

    // Both BTC and ETH drop 4% ($100 -> $96) respecting K+1=5 per-slot clamp (<= 0.75%/slot)
    let cu_oracle = step_two_oracles(&mut svm, prog_id, btc_mkt, &btc_oracle, eth_mkt, &eth_oracle, 96 * POS_SCALE, &payer);
    // Bob (ETH loser) refreshes ETH -> credits R_ETH += $20
    let cu_refresh = send_ok(&mut svm, ix_refresh_leg(prog_id, dex, eth_mkt, bob_pfl, false), &payer, &[&payer]);
    // Alice atomically runs [RefreshLeg(ETH), RefreshLeg(BTC)] in ONE tx!
    send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, eth_mkt, alice_pfl, false),
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
        ],
        &payer,
        &[&payer],
    );
    assert_eq!(pfl_total_capital(&svm, &alice_pfl), 100 * POS_SCALE, "Alice hedged spread capital must remain EXACTLY $100!");
    send_err(&mut svm, ix_liquidate(prog_id, dex, btc_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Healthy hedged Alice cannot be liquidated");

    // Both BTC and ETH drop another 4% ($96 -> $92.16)
    step_two_oracles(&mut svm, prog_id, btc_mkt, &btc_oracle, eth_mkt, &eth_oracle, 92_160_000, &payer);
    send_ok(&mut svm, ix_refresh_leg(prog_id, dex, eth_mkt, bob_pfl, false), &payer, &[&payer]);
    send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, eth_mkt, alice_pfl, false),
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
        ],
        &payer,
        &[&payer],
    );
    assert_eq!(pfl_total_capital(&svm, &alice_pfl), 100 * POS_SCALE, "Alice hedged spread survives 7.84% drop with $100 capital!");

    // Verify same-slot freshness on WithdrawCollateral!
    let s3_wdr = get_slot(&svm) + 1;
    set_slot(&mut svm, s3_wdr);
    send_err(
        &mut svm,
        ix_withdraw_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        &payer,
        &[&payer, &alice],
        "WithdrawCollateral with stale legs must fail",
    );
    // Atomic [RefreshLeg(BTC), RefreshLeg(ETH), WithdrawCollateral($5)] SUCCEEDS!
    let cu_wdr = send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
            ix_refresh_leg(prog_id, dex, eth_mkt, alice_pfl, false),
            ix_withdraw_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        ],
        &payer,
        &[&payer, &alice],
    );
    assert_eq!(pfl_total_capital(&svm, &alice_pfl), 95 * POS_SCALE);
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &all_pfls, "post-hyperliquid-spread");
    println!(
        "[PASS] Suite 3: Hyperliquid Hedged Spread + Same-Slot Freshness (dep={} CU, trade={} CU, oracle={} CU, refresh={} CU, atomic-wdr={} CU)",
        cu_dep, cu_trade, cu_oracle, cu_refresh, cu_wdr
    );

    // =========================================================================
    // SUITE 4: Truly Permissionless Cross-Margin Containment + Bug 1B / 1C + Stale-Leg Non-Blocking!
    //   4A: Alice crosses permissionless adversarial `SCAM` with `BTC` in the SAME 8-leg portfolio!
    //       - Verifies stale `SCAM` oracle CANNOT DoS-freeze `RefreshLeg(SCAM)` or `Liquidate(BTC)`!
    //       - Verifies bankrupt partial liquidation forces full close (`Bug 1C`), `SCAM` attacker
    //         extraction is strictly bounded by `R_SCAM`, unrelated `Bob`'s BTC PnL/capital is
    //         100% untouched, AND `I_BTC` / `I_ETH` are 100% BIT-FOR-BIT UNTOUCHED!
    //   4B: Bug 1B full-capital no-shielding regression across 3 permissionless cross-margin markets
    //       (`SOL + BTC2 + RUG`): bankrupt portfolio drains 100% of `capital` to 0 before `I_SOL`
    //       pays ONLY the exact true $20 shortfall (zero shielding behind BTC2 or RUG!).
    // =========================================================================
    // Close Alice's ETH leg cleanly so Alice has Long 5 BTC in `alice_pfl` ($95 cap, IM=$46.08)
    send_ok(&mut svm, ix_trade(prog_id, dex, eth_mkt, bob_pfl, bob.pubkey(), alice_pfl, alice.pubkey(), 1, 5 * POS_SCALE), &payer, &[&payer, &bob, &alice]);
    send_ok(&mut svm, ix_refresh_leg(prog_id, dex, btc_mkt, bob_pfl, false), &payer, &[&payer]);

    // Truly permissionless cross-margin: Alice crosses Long 5 BTC + Short 2 SCAM in the SAME portfolio `alice_pfl`!
    send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
            ix_trade(prog_id, dex, scam_mkt, attacker_pfl, attacker.pubkey(), alice_pfl, alice.pubkey(), 0, 2 * POS_SCALE),
        ],
        &payer,
        &[&payer, &attacker, &alice],
    );
    assert_eq!(read_u8(&svm, &alice_pfl, 4), 2, "Alice holds BOTH BTC and permissionless SCAM in one cross-margin portfolio!");

    // Stale-oracle non-blocking regression: even if permissionless `SCAM` goes stale (`age > maxStaleness`),
    // `RefreshLeg(SCAM)` STILL succeeds (dK = 0) so `SCAM` can NEVER DoS-block `BTC` operations!
    {
        let stale_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let stale_orc = Keypair::new();
        svm.airdrop(&stale_orc.pubkey(), 10_000_000_000).unwrap();
        send_ok(&mut svm, ix_create_market(prog_id, dex, stale_mkt, mint, stale_orc.pubkey(), attacker.pubkey(), attacker_tok, fee_vault,
            100 * POS_SCALE, 10, 5, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &attacker]);
        let st_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        send_ok(&mut svm, ix_init_portfolio(prog_id, dex, st_pfl, alice.pubkey()), &payer, &[&payer, &alice]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, st_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &payer, &[&payer, &alice]);
        send_ok(&mut svm, ix_trade(prog_id, dex, stale_mkt, st_pfl, alice.pubkey(), attacker_pfl, attacker.pubkey(), 0, POS_SCALE), &payer, &[&payer, &alice, &attacker]);
        let sl_now = get_slot(&svm);
        set_slot(&mut svm, sl_now + 10); // > stale_mkt maxStaleness(5)!
        // RefreshLeg on stale market MUST succeed (never DoS-blocks other legs in the portfolio!)
        send_ok(&mut svm, ix_refresh_leg(prog_id, dex, stale_mkt, st_pfl, false), &payer, &[&payer]);
        // Wind down & clean up stale_mkt so global invariants stay clean
        send_ok(&mut svm, ix_start_wind_down(prog_id, stale_mkt, keeper.pubkey()), &payer, &[&payer, &keeper]);
        set_slot(&mut svm, sl_now + 25);
        send_ok(&mut svm, ix_force_close_pair(prog_id, dex, stale_mkt, st_pfl, attacker_pfl), &payer, &[&payer]);
        send_ok(&mut svm, ix_resolve_market(prog_id, dex, stale_mkt), &payer, &[&payer]);
        send_ok(&mut svm, ix_tombstone_market(prog_id, stale_mkt), &payer, &[&payer]);
        // Refresh BTC/ETH/SCAM oracles so they remain fresh after the 25-slot jump
        send_ok(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 92_160_000, 0, 0), &payer, &[&payer, &btc_oracle]);
        send_ok(&mut svm, ix_update_oracle(prog_id, eth_mkt, eth_oracle.pubkey(), 92_160_000, 0, 0), &payer, &[&payer, &eth_oracle]);
        send_ok(&mut svm, ix_update_oracle(prog_id, scam_mkt, scam_oracle.pubkey(), 100 * POS_SCALE, 0, 0), &payer, &[&payer, &scam_oracle]);
        // Close st_pfl cleanly
        let st_rem = read_u64(&svm, &st_pfl, 88);
        send_ok(&mut svm, ix_withdraw_collateral(prog_id, dex, st_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, st_rem), &payer, &[&payer, &alice]);
        send_ok(&mut svm, ix_close_account(prog_id, st_pfl, alice.pubkey(), keeper.pubkey()), &payer, &[&payer, &alice]);
        send_ok(&mut svm, ix_close_account(prog_id, stale_mkt, attacker.pubkey(), keeper.pubkey()), &payer, &[&payer, &attacker]);
    }

    let btc_ins_before = read_u64(&svm, &btc_mkt, 224);
    let eth_ins_before = read_u64(&svm, &eth_mkt, 224);
    let bob_cap_before = pfl_total_capital(&svm, &bob_pfl);
    let btc_mid = read_u64(&svm, &btc_mkt, 8);
    let scam_mid = read_u64(&svm, &scam_mkt, 8);
    let alice_btc_lock_before = leg_locked_mm_for_mkt(&svm, &alice_pfl, btc_mid);
    assert!(alice_btc_lock_before > 0, "Alice BTC leg must hold lockedMm firewall before SCAM pump!");

    // Attacker pumps SCAM from $100 -> $180 respecting K+1=5 per-slot clamp (loss $160 > $95 -> alice_pfl bankrupt on SCAM!)
    step_oracle(&mut svm, prog_id, scam_mkt, &scam_oracle, 180 * POS_SCALE, &payer);
    let slot_post_scam = get_slot(&svm) + 1;
    set_slot(&mut svm, slot_post_scam);
    send_ok(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 92_160_000, 0, 0), &payer, &[&payer, &btc_oracle]);

    // Bug 1C + Multi-Market Firewall check: Requesting PARTIAL liquidation (`reqQty = 1.0 < 2.0`) on bankrupt
    // `alice_pfl`'s SCAM leg MUST force FULL SCAM leg close (`rawBasis == 0`), drain `freeCapital` & `SCAM.lockedMm`
    // to 0, while preserving `BTC.lockedMm` 100% INTACT and leaving `I_BTC` & `I_ETH` BIT-FOR-BIT UNTOUCHED!
    let cu_liq = send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
            ix_liquidate_ext(prog_id, dex, scam_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID,
                0, 1 * POS_SCALE, None),
        ],
        &payer,
        &[&payer],
    );
    assert_eq!(pfl_free_capital(&svm, &alice_pfl), 0, "Bug 1B: bankrupt cross-margin portfolio freeCapital == 0");
    assert_eq!(leg_locked_mm_for_mkt(&svm, &alice_pfl, scam_mid), 0, "Bug 1B: bankrupt SCAM leg lockedMm == 0");
    assert_eq!(leg_locked_mm_for_mkt(&svm, &alice_pfl, btc_mid), alice_btc_lock_before, "MULTI-MARKET FIREWALL: SCAM bankruptcy MUST NOT touch BTC.lockedMm!");
    assert_eq!(read_u8(&svm, &alice_pfl, 4), 1, "Bug 1C: bankrupt partial SCAM liq MUST force full close of SCAM leg (only BTC remains)!");
    // Unrelated honest Bob (no SCAM leg) & I_BTC / I_ETH are 100% BIT-FOR-BIT UNTOUCHED!
    assert_eq!(pfl_total_capital(&svm, &bob_pfl), bob_cap_before, "Unrelated user Bob capital untouched by SCAM!");
    assert_eq!(read_u64(&svm, &btc_mkt, 224), btc_ins_before, "I_BTC must be bit-for-bit untouched!");
    assert_eq!(read_u64(&svm, &eth_mkt, 224), eth_ins_before, "I_ETH must be bit-for-bit untouched!");
    // Top up Alice's BTC portfolio ($100) so Alice's BTC leg remains healthy for Suite 5+!
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &alice]);
    send_err(&mut svm, ix_liquidate(prog_id, dex, btc_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Alice re-margined BTC leg is healthy!");

    // Attacker claims paper profits on SCAM via ClearDeadLeg + RefreshLeg(forceHaircut=true)
    // Strictly bounded by R_SCAM!
    let scam_r_before = read_u64(&svm, &scam_mkt, 216);
    let attacker_cap_before = pfl_total_capital(&svm, &attacker_pfl);
    send_ok(&mut svm, ix_clear_dead_leg(prog_id, dex, scam_mkt, attacker_pfl), &payer, &[&payer]);
    send_ok(&mut svm, ix_refresh_leg_signed(prog_id, dex, scam_mkt, attacker_pfl, attacker.pubkey(), true), &payer, &[&payer, &attacker]);
    let attacker_gain = pfl_total_capital(&svm, &attacker_pfl) - attacker_cap_before;
    assert!(attacker_gain <= scam_r_before, "Attacker extracted {} > R_SCAM ({})!", attacker_gain, scam_r_before);
    assert_eq!(read_u64(&svm, &btc_mkt, 224), btc_ins_before, "I_BTC still untouched after Attacker claim!");
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &all_pfls, "post-scam-containment");

    // 4B: Bug 1B + Multi-Market Firewall Regression (3 Permissionless Cross-Margin Markets `SOL` + `BTC2` + `RUG`)
    //     Alice1 holds Long 10 SOL (mm=$50) + Long 9 BTC2 (mm=$45) + Long 10 RUG (mm=$0.50) on $200 capital:
    //     `freeCapital = $104.50`, `SOL.lockedMm = $50`, `BTC2.lockedMm = $45`, `RUG.lockedMm = $0.50`.
    //     SOL crashes -$220 (> $154.50 SOL-accessible equity -> exact shortfall = $65.50).
    //     Firewall drains `freeCapital` & `SOL.lockedMm` to EXACT 0 (Bug 1B: zero shielding!),
    //     while preserving `BTC2.lockedMm == $45` and `RUG.lockedMm == $0.50` BIT-FOR-BIT INTACT!
    {
        let s_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (s_vault, s_bump) = derive_dex_vault(&prog_id, &s_dex);
        send_ok(&mut svm, ix_init_dex(prog_id, s_dex, dex_admin.pubkey(), mint, s_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, s_bump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let sol_orac = Keypair::new();
        let btc2_orac = Keypair::new();
        let rug_orac = Keypair::new();
        let sol_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let btc2_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let rug_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let sol_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(&mut svm, ix_create_market(prog_id, s_dex, sol_mkt, mint, sol_orac.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        send_ok(&mut svm, ix_create_market(prog_id, s_dex, btc2_mkt, mint, btc2_orac.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        send_ok(&mut svm, ix_create_market(prog_id, s_dex, rug_mkt, mint, rug_orac.pubkey(), attacker.pubkey(), attacker_tok, fee_vault, POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &attacker]);
        send_ok(&mut svm, ix_deposit_insurance(prog_id, s_dex, sol_mkt, sol_ins, lp.pubkey(), lp_tok, mint, s_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);

        let a1 = Keypair::new(); let b1 = Keypair::new();
        let a1_tok = create_tok_acc(&mut svm, &mint, &a1.pubkey(), 1_000 * POS_SCALE);
        let b1_tok = create_tok_acc(&mut svm, &mint, &b1.pubkey(), 2_000 * POS_SCALE);
        let a1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let b1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        for (p, u, t, amt) in [(a1_pfl, &a1, a1_tok, 200 * POS_SCALE), (b1_pfl, &b1, b1_tok, 1_000 * POS_SCALE)] {
            send_ok(&mut svm, ix_init_portfolio(prog_id, s_dex, p, u.pubkey()), &payer, &[&payer, u]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, s_dex, p, u.pubkey(), t, mint, s_vault, TOKEN_PROGRAM_ID, amt), &payer, &[&payer, u]);
        }
        send_ok(&mut svm, ix_trade(prog_id, s_dex, sol_mkt, a1_pfl, a1.pubkey(), b1_pfl, b1.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &a1, &b1]);
        send_ok(&mut svm, ix_trade(prog_id, s_dex, btc2_mkt, a1_pfl, a1.pubkey(), b1_pfl, b1.pubkey(), 0, 9 * POS_SCALE), &payer, &[&payer, &a1, &b1]);
        send_ok(&mut svm, ix_trade(prog_id, s_dex, rug_mkt, a1_pfl, a1.pubkey(), b1_pfl, b1.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &a1, &b1]);
        assert_eq!(read_u8(&svm, &a1_pfl, 4), 3, "4B: Alice1 crosses SOL + BTC2 + permissionless RUG in 1 portfolio!");
        let sol_mid = read_u64(&svm, &sol_mkt, 8);
        let btc2_mid = read_u64(&svm, &btc2_mkt, 8);
        let rug_mid = read_u64(&svm, &rug_mkt, 8);
        assert_eq!(leg_locked_mm_for_mkt(&svm, &a1_pfl, sol_mid), 50 * POS_SCALE);
        assert_eq!(leg_locked_mm_for_mkt(&svm, &a1_pfl, btc2_mid), 45 * POS_SCALE);
        assert_eq!(leg_locked_mm_for_mkt(&svm, &a1_pfl, rug_mid), 500_000);
        assert_eq!(pfl_free_capital(&svm, &a1_pfl), 104_500_000);

        // Crash SOL from $100 -> $78 respecting K+1=5 per-slot clamp (-$220 loss on Long 10 SOL > $154.50 SOL-accessible equity -> shortfall = $65.50!)
        step_oracle(&mut svm, prog_id, sol_mkt, &sol_orac, 78 * POS_SCALE, &payer);
        let sol_ins_pre = read_u64(&svm, &sol_mkt, 224);
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, s_dex, btc2_mkt, a1_pfl, false),
            ix_refresh_leg(prog_id, s_dex, rug_mkt, a1_pfl, false),
            ix_liquidate(prog_id, s_dex, sol_mkt, a1_pfl, keeper_tok, mint, s_vault, TOKEN_PROGRAM_ID),
        ], &payer, &[&payer]);
        // Bug 1B + Firewall assertion: Alice1's `freeCapital` & `SOL.lockedMm` MUST be drained to EXACT 0,
        // `BTC2.lockedMm == $45` & `RUG.lockedMm == $0.50` MUST remain 100% isolated, and `I_SOL` pays exact $65.50!
        assert_eq!(pfl_free_capital(&svm, &a1_pfl), 0, "Bug 1B: freeCapital MUST be 0 whenever I_SOL is drawn!");
        assert_eq!(leg_locked_mm_for_mkt(&svm, &a1_pfl, sol_mid), 0, "Bug 1B: SOL.lockedMm MUST be 0 whenever I_SOL is drawn!");
        assert_eq!(leg_locked_mm_for_mkt(&svm, &a1_pfl, btc2_mid), 45 * POS_SCALE, "Firewall: BTC2.lockedMm 100% protected from SOL crash!");
        assert_eq!(leg_locked_mm_for_mkt(&svm, &a1_pfl, rug_mid), 500_000, "Firewall: RUG.lockedMm 100% protected from SOL crash!");
        let ins_drawn = sol_ins_pre - read_u64(&svm, &sol_mkt, 224);
        assert_eq!(ins_drawn, 65_500_000, "I_SOL pays exact $65.50 shortfall ($220 - $104.50 free - $50 SOL.lockedMm)!");
        // Bob1 receives 100% of his $220 SOL profit ($154.50 from Alice1 + $65.50 from I_SOL)!
        send_ok(&mut svm, ix_refresh_leg(prog_id, s_dex, sol_mkt, b1_pfl, false), &payer, &[&payer]);
        assert_eq!(pfl_total_capital(&svm, &b1_pfl), 1_220 * POS_SCALE, "Bob1 receives exact +$220 SOL profit!");
        assert_dex_invariants(&svm, &s_dex, &s_vault, &[sol_mkt, btc2_mkt, rug_mkt], &[a1_pfl, b1_pfl], "4B-post-bug1b-firewall");
    }
    // Restore clock slot to slot_post_scam for Suite 5 (4B used isolated s_dex)
    set_slot(&mut svm, slot_post_scam);
    println!(
        "[PASS] Suite 4: Permissionless 8-Leg Cross-Margin + Stale-Leg Non-Blocking + Bug 1B/1C (Zero Shielding, Zero Cross-Ins Leak, liq={} CU!)",
        cu_liq
    );

    // =========================================================================
    // SUITE 5: Security Regression Tests (All 5 Hardened Attack Vectors)
    // =========================================================================
    // 5a. Same-slot UpdateOracle spam rejected (slot_post_scam already updated BTC!)
    send_err(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 93_000_000, 0, 0), &payer, &[&payer, &btc_oracle], "Same-slot UpdateOracle spam");
    // 5b. Unclamped oracle jump rejected (+10% > 0.95%)
    set_slot(&mut svm, slot_post_scam + 1);
    send_err(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 102_000_000, 0, 0), &payer, &[&payer, &btc_oracle], "Unclamped oracle jump");
    // 5c. Real executable noop.so TokenProg + wrong mint + wrong vault MUST fail with exact PErr codes!
    //     (Regression test for Bug A0: executable fake token program returning Ok(0) on CPI!)
    let fake_mint = Keypair::new().pubkey();
    let fake_vault = create_tok_acc(&mut svm, &mint, &attacker.pubkey(), 0);
    let alice_cap_before_a0 = read_u64(&svm, &alice_pfl, 88);
    send_err_custom(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, fake_tok_prog, 1_000_000_000), &payer, &[&payer, &alice], 120, "Deposit with real executable noop.so tokenProg");
    assert_eq!(read_u64(&svm, &alice_pfl, 88), alice_cap_before_a0, "Phantom collateral minted via noop.so!");
    send_err_custom(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, fake_mint, dex_vault, TOKEN_PROGRAM_ID, 1_000), &payer, &[&payer, &alice], 112, "Deposit with wrong mint");
    send_err_custom(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, fake_vault, TOKEN_PROGRAM_ID, 1_000), &payer, &[&payer, &alice], 113, "Deposit with wrong vaultPda");
    send_err_custom(&mut svm, ix_withdraw_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, mint, dex_vault, fake_tok_prog, 1000), &payer, &[&payer, &bob], 120, "Withdraw with real executable noop.so tokenProg");
    send_err_custom(&mut svm, ix_withdraw_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, fake_mint, dex_vault, TOKEN_PROGRAM_ID, 1000), &payer, &[&payer, &bob], 112, "Withdraw with wrong mint");
    send_err_custom(&mut svm, ix_withdraw_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, mint, fake_vault, TOKEN_PROGRAM_ID, 1000), &payer, &[&payer, &bob], 113, "Withdraw with wrong vaultPda");
    send_err_custom(&mut svm, ix_deposit_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, fake_tok_prog, 1000), &payer, &[&payer, &lp], 120, "DepositInsurance with real executable noop.so tokenProg");
    send_err_custom(&mut svm, ix_withdraw_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, fake_tok_prog, 1000), &payer, &[&payer, &lp], 120, "WithdrawInsurance with real executable noop.so tokenProg");
    send_err_custom(&mut svm, ix_liquidate(prog_id, dex, btc_mkt, alice_pfl, keeper_tok, mint, dex_vault, fake_tok_prog), &payer, &[&payer], 120, "Liquidate with real executable noop.so tokenProg");
    // 5d. Aliased Trade rejected
    send_err(&mut svm, ix_trade(prog_id, dex, eth_mkt, bob_pfl, bob.pubkey(), bob_pfl, bob.pubkey(), 0, POS_SCALE), &payer, &[&payer, &bob], "Aliased Trade");
    // 5e. WithdrawInsurance while OI > 0 rejected (BTC still has 5 OI!)
    send_err(&mut svm, ix_withdraw_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 1000), &payer, &[&payer, &lp], "WithdrawInsurance with OI > 0");
    println!("[PASS] Suite 5: All 5 Runtime Security Regression Tests Rejected Cleanly!");

    // =========================================================================
    // SUITE 6: Post-ADL ClearDeadLeg + Full WindDown -> ForceClosePair ->
    //          ResolveMarket -> ClaimResolved -> WithdrawInsurance -> Tombstone!
    // =========================================================================
    let adl_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let adl_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, adl_mkt, mint, adl_oracle.pubkey(), lp.pubkey(), lp_tok, fee_vault,
            100 * POS_SCALE, 10, 20, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, adl_mkt, adl_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp]);

    let t1 = Keypair::new();
    let t2 = Keypair::new();
    svm.airdrop(&t1.pubkey(), 10_000_000_000).unwrap();
    svm.airdrop(&t2.pubkey(), 10_000_000_000).unwrap();
    let t1_tok = create_tok_acc(&mut svm, &mint, &t1.pubkey(), 1_000 * POS_SCALE);
    let t2_tok = create_tok_acc(&mut svm, &mint, &t2.pubkey(), 1_000 * POS_SCALE);
    let t1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let t2_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, t1_pfl, t1.pubkey()), &payer, &[&payer, &t1]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, t2_pfl, t2.pubkey()), &payer, &[&payer, &t2]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, t1_pfl, t1.pubkey(), t1_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 15 * POS_SCALE), &payer, &[&payer, &t1]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, t2_pfl, t2.pubkey(), t2_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &t2]);

    // T1 (Long 1 @ $100, cap=$15) vs T2 (Short 1 @ $100)
    send_ok(&mut svm, ix_trade(prog_id, dex, adl_mkt, t1_pfl, t1.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE), &payer, &[&payer, &t1, &t2]);
    // Crash price to $85 respecting K=4 per-slot clamp so T1 drops below MM and gets liquidated!
    step_oracle(&mut svm, prog_id, adl_mkt, &adl_oracle, 85 * POS_SCALE, &payer);
    send_ok_assert_log(&mut svm, ix_liquidate(prog_id, dex, adl_mkt, t1_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Program log: 0x3,");
    assert_eq!(read_u64(&svm, &adl_mkt, 256), 0); // oiLong == 0
    assert_eq!(read_u64(&svm, &adl_mkt, 280), POS_SCALE); // rawBasisShort == 1.0 (dead leg!)
    // WithdrawInsurance MUST fail while dead leg rawBasis > 0!
    send_err(&mut svm, ix_withdraw_insurance(prog_id, dex, adl_mkt, adl_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp], "WithdrawInsurance while dead rawBasis > 0");
    // ClearDeadLeg resets rawBasisShort -> 0 AND adlShort -> ADL_ONE!
    let cu_clear = send_ok(&mut svm, ix_clear_dead_leg(prog_id, dex, adl_mkt, t2_pfl), &payer, &[&payer]);
    assert_eq!(read_u64(&svm, &adl_mkt, 280), 0);
    assert_eq!(read_u64(&svm, &adl_mkt, 296), ADL_ONE);

    // Market recovered! Re-open a fresh pair (T1 adds collateral, opens Long 1 vs T2 Short 1),
    // then burn admin, go stale -> permissionless WindDown -> ForceClosePair -> Resolve -> WithdrawIns -> Tombstone!
    send_ok_assert_log(&mut svm, ix_deposit_collateral(prog_id, dex, t1_pfl, t1.pubkey(), t1_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &payer, &[&payer, &t1], "Program log: 0x4,");
    send_ok(&mut svm, ix_trade(prog_id, dex, adl_mkt, t1_pfl, t1.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE), &payer, &[&payer, &t1, &t2]);
    send_ok(&mut svm, ix_burn_market_admin(prog_id, adl_mkt, lp.pubkey()), &payer, &[&payer, &lp]);
    send_err(&mut svm, ix_start_wind_down(prog_id, adl_mkt, keeper.pubkey()), &payer, &[&payer, &keeper], "StartWindDown while oracle fresh");

    // Advance slot past maxStaleness (20) -> permissionless WindDown!
    let s6_wd = get_slot(&svm) + 25;
    set_slot(&mut svm, s6_wd);
    send_ok(&mut svm, ix_start_wind_down(prog_id, adl_mkt, keeper.pubkey()), &payer, &[&payer, &keeper]);
    send_err(&mut svm, ix_force_close_pair(prog_id, dex, adl_mkt, t1_pfl, t2_pfl), &payer, &[&payer], "ForceClosePair during exitWindow");
    // Advance past exitWindow (10) -> permissionless ForceClosePair!
    set_slot(&mut svm, s6_wd + 12);
    send_ok_assert_log(&mut svm, ix_force_close_pair(prog_id, dex, adl_mkt, t1_pfl, t2_pfl), &payer, &[&payer], "Program log: 0x6,");
    send_ok_assert_log(&mut svm, ix_resolve_market(prog_id, dex, adl_mkt), &payer, &[&payer], "Program log: 0x7,");
    // If T2 still has any unclaimed posPnl leg on adl_mkt, claim it!
    let _ = send_ixs_try(&mut svm, &[ix_claim_resolved(prog_id, dex, adl_mkt, t2_pfl)], &payer, &[&payer]);
    send_ok(&mut svm, ix_withdraw_insurance(prog_id, dex, adl_mkt, adl_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_tombstone_market(prog_id, adl_mkt), &payer, &[&payer]);
    assert_eq!(read_u8(&svm, &adl_mkt, 4), 3); // STATUS_TOMBSTONED
    send_err(&mut svm, ix_burn_market_admin(prog_id, adl_mkt, lp.pubkey()), &payer, &[&payer, &lp], "BurnAdmin on tombstoned market");

    // Test CloseAccount rent reclaim on empty InsReceipt, empty Portfolio, and Tombstoned Market!
    // 6a. Reject closing non-empty Portfolio (t1_pfl still has capital > 0!)
    send_err(&mut svm, ix_close_account(prog_id, t1_pfl, t1.pubkey(), keeper.pubkey()), &payer, &[&payer, &t1], "Close non-empty Portfolio");
    // 6b. Empty t1_pfl (withdraw remaining capital) and close it + reclaim rent!
    let t1_rem = read_u64(&svm, &t1_pfl, 88);
    if t1_rem > 0 {
        send_ok_assert_log(&mut svm, ix_withdraw_collateral(prog_id, dex, t1_pfl, t1.pubkey(), t1_tok, mint, dex_vault, TOKEN_PROGRAM_ID, t1_rem), &payer, &[&payer, &t1], "Program log: 0x5,");
    }
    let keeper_lam_0 = svm.get_account(&keeper.pubkey()).unwrap().lamports;
    let cu_close = send_ok(&mut svm, ix_close_account(prog_id, t1_pfl, t1.pubkey(), keeper.pubkey()), &payer, &[&payer, &t1]);
    assert_eq!(svm.get_account(&t1_pfl).map(|a| a.lamports).unwrap_or(0), 0);
    // Close empty adl_ins receipt (0 shares) & Tombstoned adl_mkt (burned admin -> permissionless)!
    send_ok(&mut svm, ix_close_account(prog_id, adl_ins, lp.pubkey(), keeper.pubkey()), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_close_account(prog_id, adl_mkt, lp.pubkey(), keeper.pubkey()), &payer, &[&payer, &lp]);
    let keeper_lam_1 = svm.get_account(&keeper.pubkey()).unwrap().lamports;
    assert_eq!(keeper_lam_1 - keeper_lam_0, 30_000_000, "All 3 closed accounts must return 100% rent!");

    let all_mkts2 = vec![btc_mkt, eth_mkt, scam_mkt];
    let all_pfls2 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts2, &all_pfls2, "post-suite6-close");
    println!("[PASS] Suite 6: Post-ADL ClearDeadLeg ({} CU) + WindDown/Tombstone + CloseAccount Rent Reclaim ({} CU)!", cu_clear, cu_close);

    // =========================================================================
    // SUITE 7 (NEW COMPOSABILITY): Bounded execPrice Spread, Authority Rotation,
    //          minMm Dust Floor, and Permissionless Insurance Donation!
    // =========================================================================
    let comp_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let comp_orc1 = Keypair::new();
    let comp_orc2 = Keypair::new();
    let comp_adm2 = Keypair::new();
    for kp in [&comp_orc1, &comp_orc2, &comp_adm2] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    // Create market with minMm = $5.00 (5_000_000) to prevent dust positions!
    send_ok(
        &mut svm,
        ix_create_market_ext(prog_id, dex, comp_mkt, mint, comp_orc1.pubkey(), lp.pubkey(), lp_tok, fee_vault,
            100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE, 5 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    // 7a. Permissionless insurance donation (donate=true, 0 LP shares minted!)
    send_ok(&mut svm, ix_deposit_insurance_ext(prog_id, dex, comp_mkt, comp_mkt, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 25 * POS_SCALE, true), &payer, &[&payer, &lp]);
    assert_eq!(read_u64(&svm, &comp_mkt, 224), 25 * POS_SCALE); // insurance == $25
    assert_eq!(read_u64(&svm, &comp_mkt, 248), 0);              // totalInsShares == 0!

    // 7b. Authority rotation: rotate oracleAuth (comp_orc1 -> comp_orc2), self-rotation back to marketAdmin ([mkt, lp, lp]),
    //     then back to comp_orc2 & transfer marketAdmin (lp -> comp_adm2)!
    send_ok(&mut svm, ix_update_market_auth(prog_id, comp_mkt, lp.pubkey(), 1, comp_orc2.pubkey()), &payer, &[&payer, &lp]);
    // Regression for Gap #4 (manual nextCursor dup resolution): rotating oracleAuth to `lp` (same key as signer `marketAdmin`!)
    // MUST succeed and set `oracleAuth == lp` cleanly (NOT corrupt `oracleAuth` with instruction bytes!)
    send_ok(&mut svm, ix_update_market_auth(prog_id, comp_mkt, lp.pubkey(), 1, lp.pubkey()), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_update_market_auth(prog_id, comp_mkt, lp.pubkey(), 1, comp_orc2.pubkey()), &payer, &[&payer, &lp]);
    let s7_orc = get_slot(&svm) + 1;
    set_slot(&mut svm, s7_orc);
    send_err(&mut svm, ix_update_oracle(prog_id, comp_mkt, comp_orc1.pubkey(), 100_700_000, 0, 0), &payer, &[&payer, &comp_orc1], "Old oracle rejected after rotation");
    send_ok(&mut svm, ix_update_oracle(prog_id, comp_mkt, comp_orc2.pubkey(), 100_700_000, 0, 0), &payer, &[&payer, &comp_orc2]);
    send_ok(&mut svm, ix_update_market_auth(prog_id, comp_mkt, lp.pubkey(), 0, comp_adm2.pubkey()), &payer, &[&payer, &lp]);
    send_err(&mut svm, ix_burn_market_admin(prog_id, comp_mkt, lp.pubkey()), &payer, &[&payer, &lp], "Old marketAdmin rejected after transfer");
    send_ok(&mut svm, ix_burn_market_admin(prog_id, comp_mkt, comp_adm2.pubkey()), &payer, &[&payer, &comp_adm2]);

    // 7c. minMm dust floor ($5.00): tiny 0.01-unit trade ($1.007 notional) needs $5.00 margin;
    //     dust portfolio with $2.00 capital is REJECTED!
    let dust_kp = Keypair::new();
    svm.airdrop(&dust_kp.pubkey(), 10_000_000_000).unwrap();
    let dust_tok = create_tok_acc(&mut svm, &mint, &dust_kp.pubkey(), 100 * POS_SCALE);
    let dust_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, dust_pfl, dust_kp.pubkey()), &payer, &[&payer, &dust_kp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, dust_pfl, dust_kp.pubkey(), dust_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 2 * POS_SCALE), &payer, &[&payer, &dust_kp]);
    send_err(&mut svm, ix_trade(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 0, 10_000), &payer, &[&payer, &dust_kp, &t2], "Dust position rejected by minMm=$5 floor");

    // 7d. Bounded execPrice spread (external CLOB/AMM/matcher fill at $101.30 vs $100.70 mark = +$0.60 spread!):
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, dust_pfl, dust_kp.pubkey(), dust_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 20 * POS_SCALE), &payer, &[&payer, &dust_kp]);
    // Out-of-band execPrice ($120 vs $100.70 > 0.75% maxMove) REJECTED!
    send_err(&mut svm, ix_trade_ext(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE, 120 * POS_SCALE), &payer, &[&payer, &dust_kp, &t2], "Out-of-band execPrice rejected");
    let dust_cap_0 = pfl_total_capital(&svm, &dust_pfl);
    let t2_cap_0 = pfl_total_capital(&svm, &t2_pfl);
    // In-band execPrice ($101.30 vs $100.70 mark, qty=1.0 -> Long pays $0.60 spread directly to Short!)
    send_ok_assert_log(&mut svm, ix_trade_ext(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE, 101_300_000), &payer, &[&payer, &dust_kp, &t2], "Program log: 0x2,");
    assert_eq!(pfl_total_capital(&svm, &dust_pfl), dust_cap_0 - 600_000, "Long must pay exact $0.60 spread to Short");
    assert_eq!(pfl_total_capital(&svm, &t2_pfl), t2_cap_0 + 600_000, "Short (LP/matcher) must receive exact $0.60 spread");

    // 7e. Donated-only market clean lifecycle: close OI -> stale WindDown -> ResolveMarket sweeps orphan $25
    //     donated insurance (totalInsShares == 0) into dex.totalSurplus -> TombstoneMarket succeeds!
    send_ok_assert_log(&mut svm, ix_trade(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 1, POS_SCALE), &payer, &[&payer, &dust_kp, &t2], "Program log: 0x2,");
    let surp_before_donate_sweep = read_u64(&svm, &dex, 192);
    set_slot(&mut svm, s7_orc + 55); // > comp_mkt lastOracleSlot + maxStaleness(50)
    send_ok(&mut svm, ix_start_wind_down(prog_id, comp_mkt, keeper.pubkey()), &payer, &[&payer, &keeper]);
    send_ok_assert_log(&mut svm, ix_resolve_market(prog_id, dex, comp_mkt), &payer, &[&payer], "Program log: 0x7,");
    assert_eq!(read_u64(&svm, &comp_mkt, 224), 0, "Orphan donated insurance must sweep to 0 on Resolve!");
    assert_eq!(read_u64(&svm, &dex, 192), surp_before_donate_sweep + 25 * POS_SCALE, "Orphan donated insurance must credit dex.totalSurplus!");
    send_ok(&mut svm, ix_tombstone_market(prog_id, comp_mkt), &payer, &[&payer]);
    assert_eq!(read_u8(&svm, &comp_mkt, 4), 3, "Donated-only market must reach STATUS_TOMBSTONED!");

    let all_mkts3 = vec![btc_mkt, eth_mkt, scam_mkt, comp_mkt];
    let all_pfls3 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl, dust_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts3, &all_pfls3, "post-suite7-composability");
    println!("[PASS] Suite 7: External Matcher execPrice Spread + Authority Rotation + minMm Floor + Donated-Insurance Tombstone + Event Logs!");

    // =========================================================================
    // SUITE 8: 1,000-STEP RANDOMIZED STATEFUL FUZZER!
    //   Fresh DEX with 3 active markets + 5 cross-margin portfolios + 1 LP.
    //   Checks EXACT `C_tot + I_tot + R_tot + S_tot == V == SPL_balance`,
    //   exact `Σ pfl.capital == C_tot`, `Σ m.insurance == I_tot`, `Σ m.realizedPool == R_tot`,
    //   `oiLong == oiShort <= rawBasis`, `adl <= ADL_ONE`, `totalMm/totalIm` coherence
    //   after EVERY SINGLE TRANSACTION!
    // =========================================================================
    let f_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (f_vault, f_bump) = derive_dex_vault(&prog_id, &f_dex);
    send_ok(&mut svm, ix_init_dex(prog_id, f_dex, dex_admin.pubkey(), mint, f_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, f_bump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);

    let s8_start = get_slot(&svm) + 10;
    set_slot(&mut svm, s8_start);
    let mut f_oracles = Vec::new();
    let mut f_mkts = Vec::new();
    let mut f_mkt_pairs = Vec::new();
    let mut f_ins_accs = Vec::new();
    let mut f_prices = [100 * POS_SCALE, 50 * POS_SCALE, 200 * POS_SCALE];
    for m_i in 0..3usize {
        let orc = Keypair::new();
        svm.airdrop(&orc.pubkey(), 10_000_000_000).unwrap();
        let mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(
            &mut svm,
            ix_create_market(prog_id, f_dex, mkt, mint, orc.pubkey(), dex_admin.pubkey(), alice_tok, fee_vault,
                f_prices[m_i], 10, 500, 0, 1000, 500, 100, 5, 75, 2500, 10_000 * POS_SCALE),
            &payer,
            &[&payer, &dex_admin],
        );
        send_ok(&mut svm, ix_deposit_insurance(prog_id, f_dex, mkt, ins, lp.pubkey(), lp_tok, mint, f_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp]);
        f_mkt_pairs.push(((m_i + 1) as u64, mkt));
        f_oracles.push(orc);
        f_mkts.push(mkt);
        f_ins_accs.push(ins);
    }

    let mut f_traders = Vec::new();
    let mut f_toks = Vec::new();
    let mut f_pfls = Vec::new();
    for _ in 0..5 {
        let kp = Keypair::new();
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
        let tok = create_tok_acc(&mut svm, &mint, &kp.pubkey(), 10_000 * POS_SCALE);
        let pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        send_ok(&mut svm, ix_init_portfolio(prog_id, f_dex, pfl, kp.pubkey()), &payer, &[&payer, &kp]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, f_dex, pfl, kp.pubkey(), tok, mint, f_vault, TOKEN_PROGRAM_ID, 80 * POS_SCALE), &payer, &[&payer, &kp]);
        f_traders.push(kp);
        f_toks.push(tok);
        f_pfls.push(pfl);
    }
    assert_dex_invariants(&svm, &f_dex, &f_vault, &f_mkts, &f_pfls, "fuzz-init");

    let mut rng = Rng(0x5EED_CAFE_2026_0001);
    let mut stats = [0u64; 8]; // [oracle, dep, wdr, open, reduce, refresh, liq, clearDead]
    let mut ok_txs = 0u64;
    let mut max_cu = 0u64;
    let mut trend_dir = [1i64, -1i64, 1i64];

    for step in 0..1000u64 {
        if step % 25 == 0 {
            for mi in 0..3 {
                trend_dir[mi] = if rng.range(2) == 0 { 1 } else { -1 };
            }
        }
        let act = rng.range(100);
        if act < 22 {
            // Advance slot + trend-biased clamped oracle move (exercises liquidations + ADL!)
            let cur = get_slot(&svm) + 1;
            set_slot(&mut svm, cur);
            let mi = rng.range(3) as usize;
            let mag = (rng.range(60) + 10) as i64; // 0.1% .. 0.69%
            let dir = if rng.range(4) == 0 { -trend_dir[mi] } else { trend_dir[mi] };
            let bps_delta = (dir * mag).clamp(-69, 69);
            let cur_p = read_u64(&svm, &f_mkts[mi], 112);
            let mut new_p = ((cur_p as i128) * (10_000 + bps_delta as i128) / 10_000) as u64;
            new_p = new_p.clamp(5 * POS_SCALE, 500 * POS_SCALE);
            let fund_sign = rng.range(2) as u8;
            let fund_e6 = rng.range(cur_p / 2000 + 1);
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_update_oracle(prog_id, f_mkts[mi], f_oracles[mi].pubkey(), new_p, fund_sign, fund_e6)], &payer, &[&payer, &f_oracles[mi]]) {
                f_prices[mi] = new_p;
                stats[0] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 28 {
            // DepositCollateral
            let ti = rng.range(5) as usize;
            let amt = (rng.range(30) + 10) * POS_SCALE;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_deposit_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_toks[ti], mint, f_vault, TOKEN_PROGRAM_ID, amt)], &payer, &[&payer, &f_traders[ti]]) {
                stats[1] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 35 {
            // Atomic [RefreshLeg..., WithdrawCollateral]
            let ti = rng.range(5) as usize;
            let amt = (rng.range(20) + 1) * POS_SCALE;
            let mut ixs = refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[ti], &f_mkt_pairs);
            ixs.push(ix_withdraw_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_toks[ti], mint, f_vault, TOKEN_PROGRAM_ID, amt));
            if let Ok(cu) = send_ixs_try(&mut svm, &ixs, &payer, &[&payer, &f_traders[ti]]) {
                stats[2] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 60 {
            // Trade Open (higher leverage: 2..6 units, with atomic pre-refresh!)
            let mi = rng.range(3) as usize;
            let tl = rng.range(5) as usize;
            let mut ts = rng.range(5) as usize;
            if ts == tl { ts = (ts + 1) % 5; }
            let qty = (rng.range(5) + 2) * POS_SCALE;
            let mut ixs = refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[tl], &f_mkt_pairs);
            ixs.extend(refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[ts], &f_mkt_pairs));
            ixs.push(ix_trade(prog_id, f_dex, f_mkts[mi], f_pfls[tl], f_traders[tl].pubkey(), f_pfls[ts], f_traders[ts].pubkey(), 0, qty));
            if let Ok(cu) = send_ixs_try(&mut svm, &ixs, &payer, &[&payer, &f_traders[tl], &f_traders[ts]]) {
                stats[3] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 72 {
            // Trade Reduce
            let mi = rng.range(3) as usize;
            let tl = rng.range(5) as usize;
            let mut ts = rng.range(5) as usize;
            if ts == tl { ts = (ts + 1) % 5; }
            let qty = (rng.range(3) + 1) * POS_SCALE;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_trade(prog_id, f_dex, f_mkts[mi], f_pfls[tl], f_traders[tl].pubkey(), f_pfls[ts], f_traders[ts].pubkey(), 1, qty)], &payer, &[&payer, &f_traders[tl], &f_traders[ts]]) {
                stats[4] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 82 {
            // RefreshLeg
            let mi = rng.range(3) as usize;
            let ti = rng.range(5) as usize;
            let force = rng.range(4) == 0;
            let res = if force {
                send_ixs_try(&mut svm, &[ix_refresh_leg_signed(prog_id, f_dex, f_mkts[mi], f_pfls[ti], f_traders[ti].pubkey(), true)], &payer, &[&payer, &f_traders[ti]])
            } else {
                send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, f_mkts[mi], f_pfls[ti], false)], &payer, &[&payer])
            };
            if let Ok(cu) = res {
                stats[5] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 93 {
            // Liquidate sweep across all markets & traders: refresh all OTHER open legs (A1),
            // leaving target market `f_mkts[mi]` for `Liquidate` itself so `shortfall > 0` triggers `I_m` draw!
            let mi = rng.range(3) as usize;
            let ti = rng.range(5) as usize;
            let other_pairs: Vec<(u64, Address)> = f_mkt_pairs.iter().copied().filter(|&(_, m)| m != f_mkts[mi]).collect();
            let mut ixs = refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[ti], &other_pairs);
            ixs.push(ix_liquidate(prog_id, f_dex, f_mkts[mi], f_pfls[ti], keeper_tok, mint, f_vault, TOKEN_PROGRAM_ID));
            if let Ok(cu) = send_ixs_try(&mut svm, &ixs, &payer, &[&payer]) {
                stats[6] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else {
            // ClearDeadLeg sweep
            let mi = rng.range(3) as usize;
            let ti = rng.range(5) as usize;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_clear_dead_leg(prog_id, f_dex, f_mkts[mi], f_pfls[ti])], &payer, &[&payer]) {
                stats[7] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        }

        // Assert EVERY SINGLE GLOBAL & LOCAL INVARIANT AFTER EVERY STEP!
        assert_dex_invariants(&svm, &f_dex, &f_vault, &f_mkts, &f_pfls, &format!("fuzz-step-{}", step));
    }

    println!(
        "[PASS] Suite 8: 1,000-Step Stateful Fuzzer — {} valid txs, ZERO invariant violations! (oracle={}, dep={}, wdr={}, open={}, red={}, ref={}, liq={}, clearDead={}, max_cu={})",
        ok_txs, stats[0], stats[1], stats[2], stats[3], stats[4], stats[5], stats[6], stats[7], max_cu
    );

    // =========================================================================
    // SUITE 9: EXTERNAL PROGRAM COMPOSITION (CPI) —
    //   9A: `oracle_adapter.so` (Permissionless external price feed + auto-clamp + funding!)
    //   9B: `matcher.so` (Passive LP AMM / Spread Matcher — single-signer Taker open & close!)
    // =========================================================================
    let matcher_path = std::env::args().nth(2).unwrap_or_else(|| "build/matcher.so".to_string());
    let adapter_path = std::env::args().nth(3).unwrap_or_else(|| "build/oracle_adapter.so".to_string());
    let matcher_elf = std::fs::read(&matcher_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", matcher_path, e));
    let adapter_elf = std::fs::read(&adapter_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", adapter_path, e));
    let matcher_prog = Keypair::new().pubkey();
    let adapter_prog = Keypair::new().pubkey();
    svm.add_program(matcher_prog, &matcher_elf).expect("matcher ELF load failed");
    svm.add_program(adapter_prog, &adapter_elf).expect("adapter ELF load failed");

    // 9A: OracleAdapter CPI composition (Custom + Pyth V2 + Chainlink OCR2 + Switchboard + 2-Leg Ratio!)
    let comp_mkt2 = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let adp_acc = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (orac_pda, orac_bump) = Address::find_program_address(&[b"orac", adp_acc.as_ref()], &adapter_prog);
    // External on-chain price feed account (32B: magic="FEED", price, conf, publishSlot)
    let feed_acc = Keypair::new().pubkey();
    let write_feed = |svm: &mut LiteSVM, price: u64, conf: u64, pub_slot: u64| {
        let mut d = vec![0u8; 32];
        d[0..4].copy_from_slice(&0x44454546u32.to_le_bytes()); // "FEED"
        d[8..16].copy_from_slice(&price.to_le_bytes());
        d[16..24].copy_from_slice(&conf.to_le_bytes());
        d[24..32].copy_from_slice(&pub_slot.to_le_bytes());
        svm.set_account(feed_acc, Account { lamports: 10_000_000, data: d, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
    };
    let s0 = get_slot(&svm) + 1;
    set_slot(&mut svm, s0);
    write_feed(&mut svm, 115 * POS_SCALE, 50_000, s0); // $115.00, conf $0.05

    // Create market with `orac_pda` (owned by OracleAdapter!) as oracleAuth!
    // (im=3000, mm=2500, liqFee=100, maxMove=400 satisfies K+1=5 exact: k5(400)+liqAtP5 = 2192+122 = 2314 <= 2500!)
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, comp_mkt2, mint, orac_pda, lp.pubkey(), lp_tok, fee_vault,
            100 * POS_SCALE, 10, 50, 0, 3000, 2500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    // InitAdapter (maxFeedAge=10, maxConfBps=100=1%, fundingBpsPerStep=10)
    let mut init_adp_data = vec![0u8; 28];
    init_adp_data[0] = 0;
    init_adp_data[1] = orac_bump;
    init_adp_data[4..12].copy_from_slice(&10u64.to_le_bytes());
    init_adp_data[12..20].copy_from_slice(&100u64.to_le_bytes());
    init_adp_data[20..28].copy_from_slice(&10u64.to_le_bytes());
    // Security regression 1: an unrelated attacker MUST NOT be able to claim/hijack an uninitialized
    // OracleAdapter bound to `comp_mkt2` (only `comp_mkt2.marketAdmin == lp` may initialize it)!
    let rogue_admin = Keypair::new();
    svm.airdrop(&rogue_admin.pubkey(), 1_000_000_000).unwrap();
    send_err_custom(
        &mut svm,
        Instruction {
            program_id: adapter_prog,
            accounts: vec![
                AccountMeta::new(adp_acc, false),
                AccountMeta::new_readonly(rogue_admin.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false),
                AccountMeta::new_readonly(comp_mkt2, false),
                AccountMeta::new_readonly(feed_acc, false),
            ],
            data: init_adp_data.clone(),
        },
        &payer,
        &[&payer, &rogue_admin],
        102, // PErr.unauthorized
        "InitAdapter must reject unrelated signer trying to hijack uninitialized market adapter",
    );
    // Security regression 2: a forged market account (not owned by `prog_id`, even with matching
    // magic + size + `rogue_admin` written at `MktOff.marketAdmin`) MUST be rejected!
    let fake_mkt = Address::new_unique();
    let mut fake_mkt_data = svm.get_account(&comp_mkt2).unwrap().data.clone();
    fake_mkt_data[56..88].copy_from_slice(rogue_admin.pubkey().as_ref());
    svm.set_account(fake_mkt, Account {
        lamports: 10_000_000,
        data: fake_mkt_data,
        owner: SYSTEM_PROGRAM_ID,
        ..Default::default()
    }).unwrap();
    {
        svm.expire_blockhash();
        let bh = svm.latest_blockhash();
        let ix = Instruction {
            program_id: adapter_prog,
            accounts: vec![
                AccountMeta::new(adp_acc, false),
                AccountMeta::new_readonly(rogue_admin.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false),
                AccountMeta::new_readonly(fake_mkt, false),
                AccountMeta::new_readonly(feed_acc, false),
            ],
            data: init_adp_data.clone(),
        };
        let tx = Transaction::new(&[&payer, &rogue_admin], Message::new(&[ix], Some(&payer.pubkey())), bh);
        let err = svm.send_transaction(tx).expect_err("InitAdapter must reject forged market account not owned by percProg");
        assert!(
            format!("{:?}", err).contains("IllegalOwner"),
            "Expected IllegalOwner for forged market account, got: {:?}",
            err
        );
    }
    send_ok(
        &mut svm,
        Instruction {
            program_id: adapter_prog,
            accounts: vec![
                AccountMeta::new(adp_acc, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false),
                AccountMeta::new_readonly(comp_mkt2, false),
                AccountMeta::new_readonly(feed_acc, false),
            ],
            data: init_adp_data,
        },
        &payer,
        &[&payer, &lp],
    );
    let ix_crank = || Instruction {
        program_id: adapter_prog,
        accounts: vec![
            AccountMeta::new_readonly(adp_acc, false),
            AccountMeta::new(comp_mkt2, false),
            AccountMeta::new_readonly(feed_acc, false),
            AccountMeta::new_readonly(orac_pda, false),
            AccountMeta::new_readonly(prog_id, false),
        ],
        data: vec![1],
    };
    // Reject stale feed, wide confidence, AND spoofed feed account owner!
    set_slot(&mut svm, s0 + 20);
    send_err(&mut svm, ix_crank(), &payer, &[&payer], "OracleAdapter rejects stale feed");
    write_feed(&mut svm, 115 * POS_SCALE, 5 * POS_SCALE, s0 + 20); // conf $5 > 1%
    send_err(&mut svm, ix_crank(), &payer, &[&payer], "OracleAdapter rejects wide confidence");
    {
        let mut spoofed = svm.get_account(&feed_acc).unwrap();
        spoofed.owner = Keypair::new().pubkey();
        let mut d = vec![0u8; 32];
        d[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
        d[8..16].copy_from_slice(&(115 * POS_SCALE).to_le_bytes());
        d[16..24].copy_from_slice(&50_000u64.to_le_bytes());
        d[24..32].copy_from_slice(&(s0 + 20).to_le_bytes());
        spoofed.data = d;
        svm.set_account(feed_acc, spoofed).unwrap();
        send_err(&mut svm, ix_crank(), &payer, &[&payer], "OracleAdapter rejects spoofed feed owner");
    }

    // Permissionless 4-slot smooth auto-clamped convergence ($100 -> $104 -> $108.16 -> $112.4864 -> $115.00)!
    let mut cu_crank = 0u64;
    for step in 1..=4u64 {
        let sl = s0 + 20 + step;
        set_slot(&mut svm, sl);
        write_feed(&mut svm, 115 * POS_SCALE, 50_000, sl);
        cu_crank = send_ok_assert_log(&mut svm, ix_crank(), &payer, &[&payer], "Program log: 0x1,");
    }
    assert_eq!(read_u64(&svm, &comp_mkt2, 112), 115 * POS_SCALE, "OracleAdapter converged smoothly to $115!");

    // 9A-2: Native Pyth V2 (`PriceUpdateV2`), Chainlink OCR2 (`Transmissions`),
    //       Switchboard On-Demand (`PullFeedAccountData`), AND 2-Leg Composite Ratio (`Pyth / Chainlink`)!
    let mut clock_now: Clock = svm.get_sysvar();
    clock_now.slot = s0 + 30;
    clock_now.unix_timestamp = 1_750_000_000;
    svm.set_sysvar(&clock_now);
    svm.expire_blockhash();

    let pyth_prog_id = Address::from_str_const("rec5EKMGg6MxZYaMdyBfgwp4d5rB9T1VQH5pJv5LtFJ");
    let cl_prog_id   = Address::from_str_const("HEvSKofvBgfaexv23kMabbYqxasxU3mQ4ibBMEmJWHny");
    let sb_prog_id   = Address::from_str_const("SBondMDrcV3K4kxZR1HNVT7osZxAHVHgYXL5Ze1oMUv");

    let make_pyth_v2 = |feed_id: [u8; 32], price: i64, conf: u64, expo: i32, pub_ts: i64, posted_slot: u64, ver: u8| -> Vec<u8> {
        let mut d = vec![0u8; 133];
        d[0..8].copy_from_slice(&[34, 241, 35, 99, 157, 126, 244, 205]);
        d[40] = ver;
        d[41..73].copy_from_slice(&feed_id);
        d[73..81].copy_from_slice(&price.to_le_bytes());
        d[81..89].copy_from_slice(&conf.to_le_bytes());
        d[89..93].copy_from_slice(&expo.to_le_bytes());
        d[93..101].copy_from_slice(&pub_ts.to_le_bytes());
        d[125..133].copy_from_slice(&posted_slot.to_le_bytes());
        d
    };
    let make_chainlink_ocr2 = |decimals: u8, live_len: u32, live_cur: u32, slot: u64, answer: i128| -> Vec<u8> {
        let mut d = vec![0u8; 200 + (live_len as usize) * 48];
        d[0..8].copy_from_slice(&[96, 179, 69, 66, 128, 129, 73, 117]);
        d[8] = 2;
        d[138] = decimals;
        d[143..147].copy_from_slice(&7u32.to_le_bytes());
        d[148..152].copy_from_slice(&live_len.to_le_bytes());
        d[152..156].copy_from_slice(&live_cur.to_le_bytes());
        let idx = ((live_cur + live_len - 1) % live_len) as usize;
        let off = 200 + idx * 48;
        d[off..off + 8].copy_from_slice(&slot.to_le_bytes());
        d[off + 16..off + 32].copy_from_slice(&answer.to_le_bytes());
        d
    };
    let make_switchboard = |value: i128, std_dev: i128, num_samples: u8, slot: u64| -> Vec<u8> {
        let mut d = vec![0u8; 3208];
        d[0..8].copy_from_slice(&[196, 27, 108, 196, 10, 215, 219, 40]);
        d[2264..2280].copy_from_slice(&value.to_le_bytes());
        d[2280..2296].copy_from_slice(&std_dev.to_le_bytes());
        d[2360] = num_samples;
        d[2368..2376].copy_from_slice(&slot.to_le_bytes());
        d
    };

    // (a) Pyth V2 Parser Test ($100 -> $103.00 at expo = -8, pinned feed_id & owner)
    let pyth_fid = [0xABu8; 32];
    let pyth_feed = Keypair::new().pubkey();
    let pyth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let pyth_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (pyth_pda, pyth_bump) = Address::find_program_address(&[b"orac", pyth_adp.as_ref()], &adapter_prog);
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_750_000_000, s0 + 30, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, pyth_mkt, mint, pyth_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 10, 50, 0, 3000, 2500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut pyth_init = vec![0u8; 60];
    pyth_init[0] = 0; pyth_init[1] = pyth_bump; pyth_init[2] = 1;
    pyth_init[4..12].copy_from_slice(&30u64.to_le_bytes());
    pyth_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    pyth_init[28..60].copy_from_slice(&pyth_fid);
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(pyth_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(pyth_mkt, false),
        AccountMeta::new_readonly(pyth_feed, false),
    ], data: pyth_init }, &payer, &[&payer, &lp]);
    let ix_pyth_crank = || Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(pyth_adp, false), AccountMeta::new(pyth_mkt, false),
        AccountMeta::new_readonly(pyth_feed, false), AccountMeta::new_readonly(pyth_pda, false),
        AccountMeta::new_readonly(prog_id, false),
    ], data: vec![1] };
    let mut c1: Clock = svm.get_sysvar(); c1.slot = s0 + 31; c1.unix_timestamp = 1_750_000_005; svm.set_sysvar(&c1);
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_750_000_000, s0 + 31, 0), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_pyth_crank(), &payer, &[&payer], 304, "Pyth rejects VerificationLevel::Partial");
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2([0xCDu8; 32], 10_300_000_000, 5_000_000, -8, 1_750_000_000, s0 + 31, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_pyth_crank(), &payer, &[&payer], 305, "Pyth rejects mismatched feed_id");
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_749_999_900, s0 + 31, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_pyth_crank(), &payer, &[&payer], 300, "Pyth rejects stale publish_time");
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_750_000_004, s0 + 31, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    let cu_pyth = send_ok_assert_log(&mut svm, ix_pyth_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &pyth_mkt, 112), 103 * POS_SCALE, "Pyth V2 parsed $103.00 (expo -8 -> E6)!");

    // (b) Chainlink OCR2 Parser Test ($100 -> $102.50, ring-buffer wraparound live_cursor=0, live_len=4, decimals=8)
    let cl_feed = Keypair::new().pubkey();
    let cl_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let cl_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (cl_pda, cl_bump) = Address::find_program_address(&[b"orac", cl_adp.as_ref()], &adapter_prog);
    svm.set_account(cl_feed, Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 0, s0 + 31, 10_250_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, cl_mkt, mint, cl_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 10, 50, 0, 3000, 2500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut cl_init = vec![0u8; 28];
    cl_init[0] = 0; cl_init[1] = cl_bump; cl_init[2] = 2;
    cl_init[4..12].copy_from_slice(&10u64.to_le_bytes());
    cl_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(cl_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(cl_mkt, false),
        AccountMeta::new_readonly(cl_feed, false),
    ], data: cl_init }, &payer, &[&payer, &lp]);
    let mut c2: Clock = svm.get_sysvar(); c2.slot = s0 + 32; c2.unix_timestamp = 1_750_000_006; svm.set_sysvar(&c2);
    let cu_cl = send_ok_assert_log(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(cl_adp, false), AccountMeta::new(cl_mkt, false),
        AccountMeta::new_readonly(cl_feed, false), AccountMeta::new_readonly(cl_pda, false),
        AccountMeta::new_readonly(prog_id, false),
    ], data: vec![1] }, &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &cl_mkt, 112), 102_500_000, "Chainlink OCR2 parsed $102.50 with ring wraparound!");

    // (c) Switchboard On-Demand Parser Test ($100 -> $104.00, full 128-bit PRECISION=18 scaling!)
    let sb_feed = Keypair::new().pubkey();
    let sb_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let sb_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (sb_pda, sb_bump) = Address::find_program_address(&[b"orac", sb_adp.as_ref()], &adapter_prog);
    let sb_val: i128 = 104i128 * 1_000_000_000_000_000_000i128;
    let sb_std: i128 = 100_000_000_000_000_000i128;
    svm.set_account(sb_feed, Account { lamports: 10_000_000, data: make_switchboard(sb_val, sb_std, 5, s0 + 32), owner: sb_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, sb_mkt, mint, sb_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 10, 50, 0, 3000, 2500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut sb_init = vec![0u8; 28];
    sb_init[0] = 0; sb_init[1] = sb_bump; sb_init[2] = 3;
    sb_init[4..12].copy_from_slice(&10u64.to_le_bytes());
    sb_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(sb_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(sb_mkt, false),
        AccountMeta::new_readonly(sb_feed, false),
    ], data: sb_init }, &payer, &[&payer, &lp]);
    let mut c3: Clock = svm.get_sysvar(); c3.slot = s0 + 33; c3.unix_timestamp = 1_750_000_007; svm.set_sysvar(&c3);
    let cu_sb = send_ok_assert_log(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(sb_adp, false), AccountMeta::new(sb_mkt, false),
        AccountMeta::new_readonly(sb_feed, false), AccountMeta::new_readonly(sb_pda, false),
        AccountMeta::new_readonly(prog_id, false),
    ], data: vec![1] }, &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &sb_mkt, 112), 104 * POS_SCALE, "Switchboard On-Demand parsed $104.00 (128-bit E18 -> E6)!");

    // (d) 2-Leg Composite Ratio Market (`Pyth V2 $500` / `Chainlink OCR2 $125` = `4.00` — e.g. STOXX/SOL!)
    let rat_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let rat_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (rat_pda, rat_bump) = Address::find_program_address(&[b"orac", rat_adp.as_ref()], &adapter_prog);
    let stoxx_feed = Keypair::new().pubkey();
    let sol_feed   = Keypair::new().pubkey();
    let stoxx_fid  = [0x55u8; 32];
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 50_000_000_000, 10_000_000, -8, 1_750_000_007, s0 + 33, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 33, 12_500_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, rat_mkt, mint, rat_pda, lp.pubkey(), lp_tok, fee_vault, 3_950_000, 10, 50, 0, 3000, 2500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut rat_init = vec![0u8; 60];
    rat_init[0] = 0; rat_init[1] = rat_bump; rat_init[2] = 1; rat_init[3] = 2;
    rat_init[4..12].copy_from_slice(&30u64.to_le_bytes());
    rat_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    rat_init[28..60].copy_from_slice(&stoxx_fid);
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(rat_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(rat_mkt, false),
        AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(sol_feed, false),
    ], data: rat_init }, &payer, &[&payer, &lp]);
    let mut c4: Clock = svm.get_sysvar(); c4.slot = s0 + 34; c4.unix_timestamp = 1_750_000_008; svm.set_sysvar(&c4);
    let cu_ratio = send_ok_assert_log(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(rat_adp, false), AccountMeta::new(rat_mkt, false),
        AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(rat_pda, false),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(sol_feed, false),
    ], data: vec![1] }, &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &rat_mkt, 112), 4 * POS_SCALE, "2-Leg Ratio Pyth($500)/Chainlink($125) converged to exact 4.00!");

    // (e) EWMA Smoothing + Hybrid After-Hours 2-Leg STOXX/SOL + Bounded PushEwmaMark!
    let ewma_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let ewma_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (ewma_pda, ewma_bump) = Address::find_program_address(&[b"orac", ewma_adp.as_ref()], &adapter_prog);
    send_ok(&mut svm, ix_create_market(prog_id, dex, ewma_mkt, mint, ewma_pda, lp.pubkey(), lp_tok, fee_vault, 4 * POS_SCALE, 10, 50, 0, 3000, 2500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut ewma_init = vec![0u8; 60];
    ewma_init[0] = 0; ewma_init[1] = ewma_bump; ewma_init[2] = 1; ewma_init[3] = 2;
    ewma_init[4..12].copy_from_slice(&30u64.to_le_bytes());
    ewma_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    ewma_init[28..60].copy_from_slice(&stoxx_fid);
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(ewma_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(ewma_mkt, false),
        AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(sol_feed, false),
    ], data: ewma_init }, &payer, &[&payer, &lp]);
    // Op 2: One-shot InitEwma (hybridAH=1, alphaBps=2000 [20%], maxDevBps=500 [5%], initEwmaPrice=$500)
    let mut init_ewma_data = vec![0u8; 26];
    init_ewma_data[0] = 2;
    init_ewma_data[1] = 1;
    init_ewma_data[2..10].copy_from_slice(&2000u64.to_le_bytes());
    init_ewma_data[10..18].copy_from_slice(&500u64.to_le_bytes());
    init_ewma_data[18..26].copy_from_slice(&(500 * POS_SCALE).to_le_bytes());
    let ix_init_ewma = Instruction {
        program_id: adapter_prog,
        accounts: vec![AccountMeta::new(ewma_adp, false), AccountMeta::new_readonly(lp.pubkey(), true)],
        data: init_ewma_data,
    };
    send_ok(&mut svm, ix_init_ewma.clone(), &payer, &[&payer, &lp]);
    send_err(&mut svm, ix_init_ewma, &payer, &[&payer, &lp], "InitEwma must be strictly one-shot immutable");

    let ix_ewma_crank = || Instruction {
        program_id: adapter_prog,
        accounts: vec![
            AccountMeta::new(ewma_adp, false), AccountMeta::new(ewma_mkt, false),
            AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(ewma_pda, false),
            AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(sol_feed, false),
        ],
        data: vec![1],
    };
    let ix_push_ewma = |signer: Address, mark_e6: u64| {
        let mut d = vec![0u8; 9];
        d[0] = 3;
        d[1..9].copy_from_slice(&mark_e6.to_le_bytes());
        Instruction {
            program_id: adapter_prog,
            accounts: vec![AccountMeta::new(ewma_adp, false), AccountMeta::new_readonly(signer, true)],
            data: d,
        }
    };

    // (e1) Live hours: STOXX jumps $500 -> $510 (fresh Pyth), SOL=$125 (fresh Chainlink)
    //      EWMA(20%) = 500*0.8 + 510*0.2 = $502.00; STOXX/SOL = 502/125 = 4.016000!
    let mut c5: Clock = svm.get_sysvar(); c5.slot = s0 + 35; c5.unix_timestamp = 1_750_000_010; svm.set_sysvar(&c5);
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 51_000_000_000, 10_000_000, -8, 1_750_000_009, s0 + 35, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 35, 12_500_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    let cu_ewma_live = send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 502 * POS_SCALE, "Live EWMA(20%) $500->$510 = $502.00!");
    assert_eq!(read_u64(&svm, &ewma_mkt, 112), 4_016_000, "Live EWMA STOXX/SOL = 502/125 = 4.016!");

    // (e2) After-hours: STOXX closes (stale by +3,600s > 30s!), SOL moves live $125 -> $128!
    //      Verify spoofed feed_id is STILL rejected, stale 24/7 quote SOL is STILL rejected,
    //      and valid after-hours Crank carries ewma(STOXX)=$502 / live(SOL)=$128 = 3.921875!
    let mut c6: Clock = svm.get_sysvar(); c6.slot = s0 + 36; c6.unix_timestamp = 1_750_003_610; svm.set_sysvar(&c6);
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2([0xEEu8; 32], 51_000_000_000, 10_000_000, -8, 1_750_000_009, s0 + 35, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 36, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_ewma_crank(), &payer, &[&payer], 305, "After-hours still rejects wrong Pyth feed_id");
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 51_000_000_000, 10_000_000, -8, 1_750_000_009, s0 + 35, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 1,  12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_ewma_crank(), &payer, &[&payer], 300, "After-hours still rejects stale 24/7 quote feed");
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 36, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    let cu_ewma_ah = send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 502 * POS_SCALE, "After-hours carries EWMA base=$502!");
    assert_eq!(read_u64(&svm, &ewma_mkt, 112), 3_921_875, "After-hours STOXX/SOL = 502/128 = 3.921875!");

    // (e3) Bounded PushEwmaMark (op=3): reject non-admin, reject >5% jump (306), accept $520 (+3.58%),
    //      reject same-slot double push (308), then permissionless Crank reprices to 505.60/128 = 3.950!
    send_err(&mut svm, ix_push_ewma(attacker.pubkey(), 510 * POS_SCALE), &payer, &[&payer, &attacker], "PushEwmaMark rejects non-admin");
    send_err_custom(&mut svm, ix_push_ewma(lp.pubkey(), 550 * POS_SCALE), &payer, &[&payer, &lp], 306, "PushEwmaMark rejects >maxDevBps jump");
    let cu_push_ewma = send_ok(&mut svm, ix_push_ewma(lp.pubkey(), 520 * POS_SCALE), &payer, &[&payer, &lp]);
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 505_600_000, "PushEwmaMark blended $502->$520 (20%) = $505.60!");
    send_err_custom(&mut svm, ix_push_ewma(lp.pubkey(), 510 * POS_SCALE), &payer, &[&payer, &lp], 308, "PushEwmaMark rejects same-slot double push");
    let mut c7: Clock = svm.get_sysvar(); c7.slot = s0 + 37; c7.unix_timestamp = 1_750_003_615; svm.set_sysvar(&c7);
    svm.set_account(sol_feed, Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 37, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_mkt, 112), 3_950_000, "After-hours Crank after PushEwmaMark = 505.60/128 = 3.950!");

    // (e4) Market re-open: Pyth STOXX resumes live at $515.60 -> EWMA smoothly blends to $507.60!
    let mut c8: Clock = svm.get_sysvar(); c8.slot = s0 + 38; c8.unix_timestamp = 1_750_003_620; svm.set_sysvar(&c8);
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 51_560_000_000, 10_000_000, -8, 1_750_003_619, s0 + 38, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 38, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 507_600_000, "Market re-open smoothly blends EWMA $505.60->$515.60 = $507.60!");
    println!(
        "       Oracle Parsers: PythV2={} CU, ChainlinkOCR2={} CU, Switchboard128={} CU, Ratio(Pyth/CL)={} CU, EWMA(live={} / AH={} / push={} CU)",
        cu_pyth, cu_cl, cu_sb, cu_ratio, cu_ewma_live, cu_ewma_ah, cu_push_ewma
    );

    // 9B: Pure 0-Signer CPI-Out PropAMM Composition (Single-Signer Taker Open & Close, 100% EOA LP Custody!)
    let comp_mkt2_mid = read_u64(&svm, &comp_mkt2, 8);
    let mtch_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
    send_ok(
        &mut svm,
        ix_init_prop_amm(matcher_prog, mtch_ctx, lp.pubkey(), 0, 50, 20, 10 * POS_SCALE, &[comp_mkt2_mid]),
        &payer,
        &[&payer, &lp],
    );
    let lp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, lp_pfl, lp.pubkey()), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_set_portfolio_matcher(prog_id, lp_pfl, lp.pubkey(), Some(mtch_ctx)), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, lp_pfl, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);

    let taker_kp = Keypair::new();
    svm.airdrop(&taker_kp.pubkey(), 10_000_000_000).unwrap();
    let taker_tok = create_tok_acc(&mut svm, &mint, &taker_kp.pubkey(), 1_000 * POS_SCALE);
    let taker_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, taker_pfl, taker_kp.pubkey()), &payer, &[&payer, &taker_kp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, taker_pfl, taker_kp.pubkey(), taker_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &taker_kp]);

    // Slippage check: ask = $115 * (1 + 90bps) = $116.035 -> limit $115.50 REJECTED (Custom(130))!
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, dex, comp_mkt2, taker_pfl, taker_kp.pubkey(), lp_pfl, matcher_prog, mtch_ctx, None, 0, true, 2 * POS_SCALE, 115_500_000),
        &payer, &[&payer, &taker_kp], 130, "Core rejects CPI-Out quote exceeding taker limitPrice",
    );
    // Single-signer Taker OPEN Long 2.0 against passive LP at Ask $116.035 (ZERO LP signature!)
    let cu_fill_open = send_ok(
        &mut svm,
        ix_trade_with_matcher(prog_id, dex, comp_mkt2, taker_pfl, taker_kp.pubkey(), lp_pfl, matcher_prog, mtch_ctx, None, 0, true, 2 * POS_SCALE, 117 * POS_SCALE),
        &payer, &[&payer, &taker_kp],
    );
    let lp_cap_after_open = pfl_total_capital(&svm, &lp_pfl);
    assert_eq!(lp_cap_after_open, 502_070_000, "LP must earn exact $2.07 spread on 2.0 open at 90bps!");

    // Pause check via Op 1 (`UpdatePropAmm`): paused PropAMM rejects quoting (Custom(200)), then unpause!
    send_ok(&mut svm, ix_update_prop_amm(matcher_prog, mtch_ctx, lp.pubkey(), 1, 50, 20, 10 * POS_SCALE), &payer, &[&payer, &lp]);
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, dex, comp_mkt2, taker_pfl, taker_kp.pubkey(), lp_pfl, matcher_prog, mtch_ctx, None, 1, true, 2 * POS_SCALE, 113 * POS_SCALE),
        &payer, &[&payer, &taker_kp], 200, "Paused PropAMM rejects quoting",
    );
    send_ok(&mut svm, ix_update_prop_amm(matcher_prog, mtch_ctx, lp.pubkey(), 0, 50, 20, 10 * POS_SCALE), &payer, &[&payer, &lp]);

    // Single-signer Taker CLOSE Long 2.0 against passive LP at standard Bid $113.965 (seller limit >= $113)!
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, dex, comp_mkt2, taker_pfl, taker_kp.pubkey(), lp_pfl, matcher_prog, mtch_ctx, None, 1, true, 2 * POS_SCALE, 114_500_000),
        &payer, &[&payer, &taker_kp], 130, "Reduce seller limitPrice rejects bid below floor",
    );
    let cu_fill_close = send_ok(
        &mut svm,
        ix_trade_with_matcher(prog_id, dex, comp_mkt2, taker_pfl, taker_kp.pubkey(), lp_pfl, matcher_prog, mtch_ctx, None, 1, true, 2 * POS_SCALE, 113 * POS_SCALE),
        &payer, &[&payer, &taker_kp],
    );
    assert_eq!(read_u64(&svm, &comp_mkt2, 256), 0, "OI must return to 0 after single-signer close!");
    assert_eq!(pfl_total_capital(&svm, &lp_pfl), 504_140_000, "LP must earn ANOTHER exact $2.07 spread on 2.0 close at Bid $113.965!");

    // LP owner withdraws $100 DIRECTLY from their EOA-owned portfolio (ZERO PDA custody!)
    let lp_tok_before = token_amount(&svm, &lp_tok);
    let cu_wdr_lp = send_ok(
        &mut svm,
        ix_withdraw_collateral(prog_id, dex, lp_pfl, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    assert_eq!(token_amount(&svm, &lp_tok) - lp_tok_before, 100 * POS_SCALE);

    let all_mkts4 = vec![btc_mkt, eth_mkt, scam_mkt, comp_mkt, comp_mkt2];
    let all_pfls4 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl, dust_pfl, lp_pfl, taker_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts4, &all_pfls4, "post-suite9-external-cpi");

    // 9C: Atomic [UpdateOracle/Crank + RefreshLeg(LP)] Anti-Reordering Bundle + K=4 Censored Envelope!
    //     1) Verifies atomic [Crank(SOL), RefreshLeg(SOL, LP), Crank(ETH), RefreshLeg(ETH, LP)]
    //        funds R_SOL in the SAME tx that moves the price, defeating adversarial-leader
    //        premature-liquidation reordering of a tight hedged spread!
    //     2) Verifies K=4 consecutive adverse oracle steps (maxMove=1%, mm=5%, liqFee=1%) with
    //        ZERO interleaved liquidations still liquidates with shortfall == 0 & I_m untouched!
    let (cu_crank_bundle, wire_crank_bundle, cu_k4_liq) = {
        let b_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (b_vault, b_bump) = derive_dex_vault(&prog_id, &b_dex);
        send_ok(&mut svm, ix_init_dex(prog_id, b_dex, dex_admin.pubkey(), mint, b_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, b_bump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let b_sol_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let b_eth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let b_sol_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let b_eth_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let (b_sol_pda, b_sol_bump) = Address::find_program_address(&[b"orac", b_sol_adp.as_ref()], &adapter_prog);
        let (b_eth_pda, b_eth_bump) = Address::find_program_address(&[b"orac", b_eth_adp.as_ref()], &adapter_prog);
        let b_sol_feed = Keypair::new().pubkey();
        let b_eth_feed = Keypair::new().pubkey();
        let write_custom = |svm: &mut LiteSVM, faddr: Address, price: u64, slot: u64| {
            let mut d = vec![0u8; 32];
            d[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
            d[8..16].copy_from_slice(&price.to_le_bytes());
            d[16..24].copy_from_slice(&10_000u64.to_le_bytes());
            d[24..32].copy_from_slice(&slot.to_le_bytes());
            svm.set_account(faddr, Account { lamports: 10_000_000, data: d, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        };
        let b_sl0 = get_slot(&svm) + 1;
        set_slot(&mut svm, b_sl0);
        write_custom(&mut svm, b_sol_feed, 100 * POS_SCALE, b_sl0);
        write_custom(&mut svm, b_eth_feed, 100 * POS_SCALE, b_sl0);
        // maxMoveBps=75 (0.75%/slot), mmBps=500 (5%), liqFeeBps=100 (1%), maxStaleness=150 -> K+1=5 compounded safe (486 <= 500)!
        send_ok(&mut svm, ix_create_market(prog_id, b_dex, b_sol_mkt, mint, b_sol_pda, dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 150, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        send_ok(&mut svm, ix_create_market(prog_id, b_dex, b_eth_mkt, mint, b_eth_pda, dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 150, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        let b_sol_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(&mut svm, ix_deposit_insurance(prog_id, b_dex, b_sol_mkt, b_sol_ins, lp.pubkey(), lp_tok, mint, b_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);
        for (adp, mkt, fd, bump) in [(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_bump), (b_eth_adp, b_eth_mkt, b_eth_feed, b_eth_bump)] {
            let mut d = vec![0u8; 28];
            d[0] = 0; d[1] = bump;
            d[4..12].copy_from_slice(&150u64.to_le_bytes());
            d[12..20].copy_from_slice(&100u64.to_le_bytes());
            send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
                AccountMeta::new(adp, false), AccountMeta::new_readonly(dex_admin.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(mkt, false),
                AccountMeta::new_readonly(fd, false),
            ], data: d }, &payer, &[&payer, &dex_admin]);
        }

        // Hedged trader holds Long 10 SOL + Short 10 ETH ($200 IM, $100 MM) on $200 capital vs LP;
        // then withdraws $100? No, keep tight: Open Long 5 SOL + Short 5 ETH ($100 IM, $50 MM) on $100 cap,
        // PLUS a 2nd unhedged trader on SOL right at MM ($50 cap, Long 10 SOL? IM=$100 so open Long 5 SOL
        // with $50 cap after IM=50 -> price drops to MM=$25, then K=4 consecutive -1% steps!).
        let h_kp = Keypair::new(); let lp_kp = Keypair::new(); let u_kp = Keypair::new();
        let h_tok = create_tok_acc(&mut svm, &mint, &h_kp.pubkey(), 1_000 * POS_SCALE);
        let lp_b_tok = create_tok_acc(&mut svm, &mint, &lp_kp.pubkey(), 5_000 * POS_SCALE);
        let u_tok = create_tok_acc(&mut svm, &mint, &u_kp.pubkey(), 1_000 * POS_SCALE);
        let h_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let lp_b_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let u_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        for (p, k, t, amt) in [(h_pfl, &h_kp, h_tok, 100 * POS_SCALE), (lp_b_pfl, &lp_kp, lp_b_tok, 2_000 * POS_SCALE), (u_pfl, &u_kp, u_tok, 100 * POS_SCALE)] {
            send_ok(&mut svm, ix_init_portfolio(prog_id, b_dex, p, k.pubkey()), &payer, &[&payer, k]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, b_dex, p, k.pubkey(), t, mint, b_vault, TOKEN_PROGRAM_ID, amt), &payer, &[&payer, k]);
        }
        send_ok(&mut svm, ix_trade(prog_id, b_dex, b_sol_mkt, h_pfl, h_kp.pubkey(), lp_b_pfl, lp_kp.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &h_kp, &lp_kp]);
        send_ok(&mut svm, ix_trade(prog_id, b_dex, b_eth_mkt, lp_b_pfl, lp_kp.pubkey(), h_pfl, h_kp.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &lp_kp, &h_kp]);
        // Unhedged trader U: Long 10 SOL ($1,000 notional, IM=$100, MM=$50) on $100 capital!
        send_ok(&mut svm, ix_trade(prog_id, b_dex, b_sol_mkt, u_pfl, u_kp.pubkey(), lp_b_pfl, lp_kp.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &u_kp, &lp_kp]);

        // Atomic Crank+LP Bundle on slot +1: both SOL and ETH jump +0.7% ($100 -> $100.70)!
        // Crank bot atomically executes [Crank(SOL), RefreshLeg(SOL, LP), Crank(ETH), RefreshLeg(ETH, LP)]
        // in ONE Solana tx so R_SOL is funded IMMEDIATELY in the same tx!
        set_slot(&mut svm, b_sl0 + 1);
        write_custom(&mut svm, b_sol_feed, 100_700_000, b_sl0 + 1);
        write_custom(&mut svm, b_eth_feed, 100_700_000, b_sl0 + 1);
        let ix_b_crank = |adp: Address, mkt: Address, fd: Address, pda: Address| Instruction {
            program_id: adapter_prog,
            accounts: vec![
                AccountMeta::new_readonly(adp, false), AccountMeta::new(mkt, false),
                AccountMeta::new_readonly(fd, false), AccountMeta::new_readonly(pda, false),
                AccountMeta::new_readonly(prog_id, false),
            ],
            data: vec![1],
        };
        let (cu_bndl, wire_bndl) = send_ixs_ok_measured(
            &mut svm,
            &[
                ix_b_crank(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_pda),
                ix_refresh_leg(prog_id, b_dex, b_sol_mkt, lp_b_pfl, false),
                ix_b_crank(b_eth_adp, b_eth_mkt, b_eth_feed, b_eth_pda),
                ix_refresh_leg(prog_id, b_dex, b_eth_mkt, lp_b_pfl, false),
            ],
            &payer,
            &[&payer],
        );
        // Hedged trader's SOL gain (+$3.50) immediately covers ETH loss (-$3.50) -> capital == $100,
        // and adversarial keeper liquidation attempt on ETH is REJECTED!
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, b_dex, b_sol_mkt, h_pfl, false),
            ix_refresh_leg(prog_id, b_dex, b_eth_mkt, h_pfl, false),
        ], &payer, &[&payer]);
        assert_eq!(pfl_total_capital(&svm, &h_pfl), 100 * POS_SCALE, "Atomic Crank+LP bundle preserved exact $100 hedged capital!");
        send_err(&mut svm, ix_liquidate(prog_id, b_dex, b_eth_mkt, h_pfl, keeper_tok, mint, b_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Hedged trader cannot be liquidated after atomic Crank+LP bundle");

        // Now test K+1=5 consecutive censored liquidation slots on unhedged U (Long 10 SOL)!
        // First push SOL down ~5.3% ($100.70 -> ~$95.36) so U sits right near MM (~$53.6 cap vs ~$47.7 MM),
        // then run K+1=5 consecutive -0.7% oracle slots WITHOUT liquidating U, then liquidate on honest slot!
        let mut p_sol = 100_700_000u64;
        for st in 2..=9u64 {
            set_slot(&mut svm, b_sl0 + st);
            p_sol = (p_sol * 993) / 1000;
            write_custom(&mut svm, b_sol_feed, p_sol, b_sl0 + st);
            send_ok(&mut svm, ix_b_crank(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_pda), &payer, &[&payer]);
        }
        // Refresh U right at MM boundary (~$52 capital vs ~$47.6 MM): still healthy!
        send_ok(&mut svm, ix_refresh_leg(prog_id, b_dex, b_sol_mkt, u_pfl, false), &payer, &[&payer]);
        let ins_before_k4 = read_u64(&svm, &b_sol_mkt, 224);
        // K+1=5 consecutive censored oracle slots (-0.7%/slot, ZERO liquidations!)
        for st in 10..=14u64 {
            set_slot(&mut svm, b_sl0 + st);
            p_sol = (p_sol * 993) / 1000;
            write_custom(&mut svm, b_sol_feed, p_sol, b_sl0 + st);
            send_ok(&mut svm, ix_b_crank(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_pda), &payer, &[&payer]);
        }
        // Honest leader arrives and liquidates U: ZERO bad debt & I_SOL bit-for-bit untouched!
        let cu_k4 = send_ok(&mut svm, ix_liquidate(prog_id, b_dex, b_sol_mkt, u_pfl, keeper_tok, mint, b_vault, TOKEN_PROGRAM_ID), &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &b_sol_mkt, 224), ins_before_k4, "K+1=5 censored oracle slots produced ZERO bad debt (I_SOL untouched)!");
        assert_dex_invariants(&svm, &b_dex, &b_vault, &[b_sol_mkt, b_eth_mkt], &[h_pfl, lp_b_pfl, u_pfl], "post-9C-atomic-bundle-and-k4");
        (cu_bndl, wire_bndl, cu_k4)
    };
    println!(
        "[PASS] Suite 9: External CPI (adapter={} B crank={} CU, matcher={} B open/close/wdr={}/{}/{} CU) + Atomic Crank+LP Bundle ({} CU, {} B) + K=4 Censored Liq ({} CU, 0 bad debt)!",
        adapter_elf.len(), cu_crank, matcher_elf.len(), cu_fill_open, cu_fill_close, cu_wdr_lp, cu_crank_bundle, wire_crank_bundle, cu_k4_liq
    );

    // =========================================================================
    // SUITE 10: CORE HARDENING + FAIR TRANSPARENT LIQUIDATIONS (NO TTP!)
    //   10a. Unbounded maxStaleness / exitWindow / warmupSlots!=0 REJECTED!
    //   10b. Trade(mode=1) execPrice cross-margin bypass REJECTED!
    //   10c. Partial Liquidation + Permissionless Counterparty Takeover (ZERO ADL!) + Gradual Fee!
    // =========================================================================
    // 10a. Unbounded parameter DoS rejections
    let bad_mkt2 = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    send_err(&mut svm, ix_create_market(prog_id, dex, bad_mkt2, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
        100 * POS_SCALE, 300_000, 50, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &alice], "exitWindow > MAX_EXIT_WINDOW rejected");
    send_err(&mut svm, ix_create_market(prog_id, dex, bad_mkt2, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
        100 * POS_SCALE, 20, 50_000, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &alice], "maxStaleness > MAX_STALENESS rejected");
    send_err(&mut svm, ix_create_market(prog_id, dex, bad_mkt2, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
        100 * POS_SCALE, 20, 50, 1, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &alice], "non-zero warmupSlots rejected");

    // 10b + 10c on fresh fair-liq market `fair_mkt` ($100, IM=10%, MM=5%, liqFee=1%, maxMove=0.75%)
    let fair_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let fair_orc = Keypair::new();
    let victim = Keypair::new();
    let hlp_lp = Keypair::new();
    let cparty = Keypair::new();
    for kp in [&fair_orc, &victim, &hlp_lp, &cparty] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    let vic_tok = create_tok_acc(&mut svm, &mint, &victim.pubkey(), 1_000 * POS_SCALE);
    let hlp_tok = create_tok_acc(&mut svm, &mint, &hlp_lp.pubkey(), 2_000 * POS_SCALE);
    let cp_tok  = create_tok_acc(&mut svm, &mint, &cparty.pubkey(), 2_000 * POS_SCALE);
    let vic_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let hlp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let cp_pfl  = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);

    send_ok(&mut svm, ix_create_market(prog_id, dex, fair_mkt, mint, fair_orc.pubkey(), lp.pubkey(), lp_tok, fee_vault,
        100 * POS_SCALE, 20, 50, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, vic_pfl, victim.pubkey()), &payer, &[&payer, &victim]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, hlp_pfl, hlp_lp.pubkey()), &payer, &[&payer, &hlp_lp]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, cp_pfl,  cparty.pubkey()), &payer, &[&payer, &cparty]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, vic_pfl, victim.pubkey(), vic_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &victim]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, hlp_pfl, hlp_lp.pubkey(), hlp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &hlp_lp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, cp_pfl,  cparty.pubkey(), cp_tok,  mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &cparty]);

    // Victim opens Long 10.0 @ $100 vs Counterparty Short 10.0
    send_ok(&mut svm, ix_trade(prog_id, dex, fair_mkt, vic_pfl, victim.pubkey(), cp_pfl, cparty.pubkey(), 0, 10 * POS_SCALE),
        &payer, &[&payer, &victim, &cparty]);

    // 10b. Verify Trade(mode=1) execPrice spread CANNOT drain payer below remaining totalMm!
    step_oracle(&mut svm, prog_id, fair_mkt, &fair_orc, 94_450_000, &payer);
    send_err(&mut svm, ix_trade_ext(prog_id, dex, fair_mkt, vic_pfl, victim.pubkey(), cp_pfl, cparty.pubkey(), 1, 10_000, 93_900_000),
        &payer, &[&payer, &victim, &cparty], "Trade(mode=1) execPrice draining below totalMm rejected");

    // 10c. Fair Partial Liquidation + Permissionless Takeover (**ZERO ADL ON INNOCENT COUNTERPARTY!**)
    let hlp_tok_0 = token_amount(&svm, &hlp_tok);
    let cu_part_take = send_ok(
        &mut svm,
        ix_liquidate_ext(prog_id, dex, fair_mkt, vic_pfl, hlp_tok, mint, dex_vault, TOKEN_PROGRAM_ID,
            1, 4 * POS_SCALE, Some((hlp_pfl, hlp_lp.pubkey()))),
        &payer,
        &[&payer, &hlp_lp],
    );
    let fee_paid = token_amount(&svm, &hlp_tok) - hlp_tok_0;
    let max_part_fee = (4 * 94_450_000u64) / 100;
    assert!(fee_paid > 0 && fee_paid < max_part_fee, "Gradual deficit fee ({}) must be strictly < maxFee ({})!", fee_paid, max_part_fee);
    assert_eq!(read_u64(&svm, &vic_pfl, LEG_HEADER + 48), 6 * POS_SCALE, "Victim must retain 6.0 units after partial liquidation!");
    assert_eq!(read_u64(&svm, &hlp_pfl, LEG_HEADER + 48), 4 * POS_SCALE, "Liquidator must hold 4.0 taken-over units!");
    assert_eq!(read_u64(&svm, &fair_mkt, 256), 10 * POS_SCALE, "OI must stay 10.0 (takeover, no OI destroy)!");
    assert_eq!(read_u64(&svm, &fair_mkt, 288), ADL_ONE, "adlLong MUST remain ADL_ONE (ZERO ADL)!");
    assert_eq!(read_u64(&svm, &fair_mkt, 296), ADL_ONE, "adlShort MUST remain ADL_ONE (ZERO ADL)!");
    send_err(&mut svm, ix_liquidate(prog_id, dex, fair_mkt, vic_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID),
        &payer, &[&payer], "Victim is healthy after partial liquidation!");

    let all_mkts5 = vec![btc_mkt, eth_mkt, scam_mkt, comp_mkt, comp_mkt2, fair_mkt];
    let all_pfls5 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl, dust_pfl, lp_pfl, taker_pfl, vic_pfl, hlp_pfl, cp_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts5, &all_pfls5, "post-suite10-fair-liq");
    println!(
        "[PASS] Suite 10: Core Hardening + Partial Permissionless Takeover ({} CU, gradual fee={} < max={}, ZERO ADL!)",
        cu_part_take, fee_paid, max_part_fee
    );

    // =========================================================================
    // SUITE 11: WORST-CASE 8-LEG (`MAX_LEGS = 8`) CU EXHAUSTION + A1 / A2 / B4
    //   Tests EVERY worst-case actor role on a FULL 8-market, 8-leg portfolio:
    //   1. A1 Selective-Liquidation Attack on an 8-leg hedged spread (REJECTED!)
    //   2. USERS: Atomic [8x RefreshLeg + WithdrawCollateral], Atomic [8x RefreshLeg + Trade],
    //             Double-8-Leg Trade (both parties holding 8 legs = 16 legs total!)
    //   3. B4 Position Hand-Off: Trade(mode=2 Long->Long) & Trade(mode=3 Short->Short) on 8-leg portfolio
    //   4. LIQUIDATION KEEPERS:
    //        - Worst-case 8-leg Tier-3 fallback: Atomic [7x RefreshLeg + Liquidate(mode=0)]
    //        - A2 Post-ADL Recovery: Post-ADL Trade(mode=0) open + Post-ADL 8-leg Takeover (mode=1)
    //          where BOTH victim (8 legs) AND liquidator (8 legs) are maxed out!
    //   5. CRANKS: 8-market UpdateOracle batch, 8-market OracleAdapter CPI crank,
    //              8-market WindDown -> ForceClosePair -> ClearDeadLeg -> ResolveMarket sweep!
    //   Verifies BOTH Solana CU budget (<= 200,000 default CU!) AND 1,232B legacy UDP packet limit!
    // =========================================================================
    let w_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (w_vault, w_bump) = derive_dex_vault(&prog_id, &w_dex);
    send_ok(
        &mut svm,
        ix_init_dex(prog_id, w_dex, dex_admin.pubkey(), mint, w_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, w_bump, 6, 0, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
    );

    let mut w_slot = get_slot(&svm) + 10;
    set_slot(&mut svm, w_slot);

    let mut w_mkts = Vec::new();
    let w_orc_shared = Keypair::new();
    svm.airdrop(&w_orc_shared.pubkey(), 10_000_000_000).unwrap();
    let mut w_mkt_pairs = Vec::new();
    let mut w_ins = Vec::new();
    let mut w_adps = Vec::new();
    let mut w_orac_pdas = Vec::new();
    let mut w_feeds = Vec::new();

    for i in 0..MAX_LEGS {
        let mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        // Market i: $100, exitWindow=10, maxStaleness=200, IM=10%, MM=5%, liqFee=1%, tradeFee=0, maxMove=0.95% (K=4 exact), insDraw=25%
        send_ok(
            &mut svm,
            ix_create_market(prog_id, w_dex, mkt, mint, w_orc_shared.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault,
                100 * POS_SCALE, 10, 200, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE),
            &payer,
            &[&payer, &dex_admin],
        );
        send_ok(
            &mut svm,
            ix_deposit_insurance(prog_id, w_dex, mkt, ins, lp.pubkey(), lp_tok, mint, w_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE),
            &payer,
            &[&payer, &lp],
        );
        // Also wire an OracleAdapter CPI feed on a second set of adapters? We can rotate oracleAuth later for crank test!
        let adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let (opda, obump) = Address::find_program_address(&[b"orac", adp.as_ref()], &adapter_prog);
        let feed = Keypair::new().pubkey();
        let mut fd = vec![0u8; 32];
        fd[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
        fd[8..16].copy_from_slice(&(100 * POS_SCALE).to_le_bytes());
        fd[16..24].copy_from_slice(&50_000u64.to_le_bytes());
        fd[24..32].copy_from_slice(&w_slot.to_le_bytes());
        svm.set_account(feed, Account { lamports: 10_000_000, data: fd, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        let mut iad = vec![0u8; 28];
        iad[0] = 0;
        iad[1] = obump;
        iad[4..12].copy_from_slice(&50u64.to_le_bytes());
        iad[12..20].copy_from_slice(&100u64.to_le_bytes());
        iad[20..28].copy_from_slice(&0u64.to_le_bytes());
        send_ok(
            &mut svm,
            Instruction {
                program_id: adapter_prog,
                accounts: vec![
                    AccountMeta::new(adp, false),
                    AccountMeta::new_readonly(dex_admin.pubkey(), true),
                    AccountMeta::new_readonly(prog_id, false),
                    AccountMeta::new_readonly(mkt, false),
                    AccountMeta::new_readonly(feed, false),
                ],
                data: iad,
            },
            &payer,
            &[&payer, &dex_admin],
        );

        w_mkts.push(mkt);
        w_mkt_pairs.push(((i + 1) as u64, mkt));
        w_ins.push(ins);
        w_adps.push(adp);
        w_orac_pdas.push(opda);
        w_feeds.push(feed);
    }

    // Create 4 portfolios on w_dex:
    //   u_pfl (User A — 8 legs!), c_pfl (Counterparty B — 8 legs!),
    //   k_pfl (Liquidation Keeper / HLP — 8 legs!), d_pfl (Helper Counterparty for keeper legs & post-ADL open)
    let w_user = Keypair::new();
    let w_cp   = Keypair::new();
    let w_keep = Keypair::new();
    let w_aux  = Keypair::new();
    for kp in [&w_user, &w_cp, &w_keep, &w_aux] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    let wu_tok = create_tok_acc(&mut svm, &mint, &w_user.pubkey(), 50_000 * POS_SCALE);
    let wc_tok = create_tok_acc(&mut svm, &mint, &w_cp.pubkey(),   50_000 * POS_SCALE);
    let wk_tok = create_tok_acc(&mut svm, &mint, &w_keep.pubkey(), 50_000 * POS_SCALE);
    let wa_tok = create_tok_acc(&mut svm, &mint, &w_aux.pubkey(),  50_000 * POS_SCALE);

    let wu_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let wc_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let wk_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let wa_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let w_all_pfls = vec![wu_pfl, wc_pfl, wk_pfl, wa_pfl];

    for (pfl, kp, tok, cap) in [
        (wu_pfl, &w_user, wu_tok, 200 * POS_SCALE), // $200 capital -> 8 legs x $200 notional = $1600 gross ($160 IM, $80 MM)!
        (wc_pfl, &w_cp,   wc_tok, 5_000 * POS_SCALE),
        (wk_pfl, &w_keep, wk_tok, 5_000 * POS_SCALE),
        (wa_pfl, &w_aux,  wa_tok, 5_000 * POS_SCALE),
    ] {
        send_ok(&mut svm, ix_init_portfolio(prog_id, w_dex, pfl, kp.pubkey()), &payer, &[&payer, kp]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, w_dex, pfl, kp.pubkey(), tok, mint, w_vault, TOKEN_PROGRAM_ID, cap), &payer, &[&payer, kp]);
    }

    // Open ALL 8 LEGS on User A (Long mkts 0..4, Short mkts 4..8, qty = 2.0 each -> $1600 notional, IM=$160, MM=$80)
    // AND ALL 8 LEGS on Counterparty B (opposite side on all 8 markets)!
    for i in 0..MAX_LEGS {
        if i < 4 {
            send_ok(&mut svm, ix_trade(prog_id, w_dex, w_mkts[i], wu_pfl, w_user.pubkey(), wc_pfl, w_cp.pubkey(), 0, 2 * POS_SCALE),
                &payer, &[&payer, &w_user, &w_cp]);
        } else {
            send_ok(&mut svm, ix_trade(prog_id, w_dex, w_mkts[i], wc_pfl, w_cp.pubkey(), wu_pfl, w_user.pubkey(), 0, 2 * POS_SCALE),
                &payer, &[&payer, &w_cp, &w_user]);
        }
    }
    // Also populate Keeper (wk_pfl) with 7 legs on mkts 1..8 (so taking over mkt 0 fills ALL 8 LEGS of Keeper!)
    for i in 1..MAX_LEGS {
        send_ok(&mut svm, ix_trade(prog_id, w_dex, w_mkts[i], wk_pfl, w_keep.pubkey(), wa_pfl, w_aux.pubkey(), 0, POS_SCALE),
            &payer, &[&payer, &w_keep, &w_aux]);
    }
    assert_eq!(read_u8(&svm, &wu_pfl, 4), 8, "User A must hold ALL 8 legs!");
    assert_eq!(read_u8(&svm, &wc_pfl, 4), 8, "Counterparty B must hold ALL 8 legs!");
    assert_eq!(read_u8(&svm, &wk_pfl, 4), 7, "Keeper must hold 7 legs before takeover!");
    assert_dex_invariants(&svm, &w_dex, &w_vault, &w_mkts, &w_all_pfls, "suite11-8leg-open");

    // 11.1 CRANK WORST-CASE: Batch 8x UpdateOracle in ONE single Solana tx!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let orc_ixs: Vec<Instruction> = (0..MAX_LEGS)
        .map(|i| ix_update_oracle(prog_id, w_mkts[i], w_orc_shared.pubkey(), 100_700_000, 0, 0))
        .collect();
    let (cu_crank_8orc, wire_8orc) = send_ixs_ok_measured(&mut svm, &orc_ixs, &payer, &[&payer, &w_orc_shared]);
    assert!(cu_crank_8orc < 200_000 && wire_8orc <= 1232, "8x UpdateOracle batch exceeded limits: {} CU, {} B", cu_crank_8orc, wire_8orc);

    // 11.2 A1 SELECTIVE LIQUIDATION ATTACK ON 8-LEG HEDGED SPREAD:
    //   All 8 markets rose +3.5% ($100 -> $103.50): User A won +$28 on mkts 0..3 and lost -$28 on mkts 4..7!
    //   First Counterparty B refreshes its losing legs (mkts 0..3) so R_m is funded for User A's winners.
    let cp_ref_win: Vec<Instruction> = (0..4).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wc_pfl, false)).collect();
    send_ixs_ok(&mut svm, &cp_ref_win, &payer, &[&payer]);
    //   Attack A1a: bare Liquidate(mkt 4, wu_pfl) WITHOUT refreshing other 7 legs -> REJECTED (`stalePortfolioLeg`)!
    send_err(&mut svm, ix_liquidate(prog_id, w_dex, w_mkts[4], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID),
        &payer, &[&payer], "A1: Selective single-leg liquidation on 8-leg hedged portfolio MUST fail");
    //   Attack A1b: Atomic [7x RefreshLeg(mkts 0..3, 5..7) + Liquidate(mkt 4)] -> REJECTED (`positionHealthy`)!
    let mut a1_ixs: Vec<Instruction> = (0..MAX_LEGS).filter(|&i| i != 4)
        .map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    a1_ixs.push(ix_liquidate(prog_id, w_dex, w_mkts[4], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID));
    send_ixs_err(&mut svm, &a1_ixs, &payer, &[&payer], "A1: Net-healthy 8-leg hedged portfolio cannot be liquidated");

    // 11.3 USER WORST-CASE 8-LEG ATOMIC WITHDRAW: [8x RefreshLeg(wu_pfl) + WithdrawCollateral($10)] in ONE tx!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut wdr8_ixs: Vec<Instruction> = (0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    wdr8_ixs.push(ix_withdraw_collateral(prog_id, w_dex, wu_pfl, w_user.pubkey(), wu_tok, mint, w_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE));
    let (cu_user_8wdr, wire_user_8wdr) = send_ixs_ok_measured(&mut svm, &wdr8_ixs, &payer, &[&payer, &w_user]);
    assert!(cu_user_8wdr < 200_000 && wire_user_8wdr <= 1232, "8-leg atomic Withdraw exceeded limits: {} CU, {} B", cu_user_8wdr, wire_user_8wdr);

    // 11.4 USER WORST-CASE 8-LEG ATOMIC TRADE:
    //   (a) Single-tx [8x RefreshLeg(wu_pfl) + Trade(wu_pfl vs wa_pfl)] — single-sided 8-leg atomic tx!
    //   (b) Double-8-leg worst case (BOTH wu_pfl AND wc_pfl hold 8 legs = 16 legs total):
    //       Check whether 17 ixs fits in 1 legacy tx (1,232B MTU) and measure both 1-tx & 2-tx same-slot CU!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut trd16_ixs: Vec<Instruction> = (0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    trd16_ixs.extend((0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wc_pfl, false)));
    trd16_ixs.push(ix_trade(prog_id, w_dex, w_mkts[0], wu_pfl, w_user.pubkey(), wc_pfl, w_cp.pubkey(), 0, POS_SCALE / 10));
    let (cu_user_16trd, wire_user_16trd) = send_ixs_ok_measured(&mut svm, &trd16_ixs, &payer, &[&payer, &w_user, &w_cp]);
    assert!(cu_user_16trd < 200_000 && wire_user_16trd <= 1232, "Double-8-leg atomic Trade exceeded limits: {} CU, {} B", cu_user_16trd, wire_user_16trd);

    // 11.5 B4 POSITION HAND-OFF (`Trade` mode=2 Long->Long & mode=3 Short->Short) ON 8-LEG PORTFOLIO!
    //   User A (8 legs) hands off 0.5 Long on mkt 0 to Keeper (who currently has 7 legs -> becomes 8 legs!)
    //   with bounded execPrice spread ($104.00 vs $103.50 mark = +$0.50/unit -> Keeper pays $0.25 to User A).
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let m0_oi_0 = read_u64(&svm, &w_mkts[0], 256);
    let m0_rl_0 = read_u64(&svm, &w_mkts[0], 272);
    let m0_adl_0 = read_u64(&svm, &w_mkts[0], 288);
    let mut ho_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wk_pfl, false)).collect();
    ho_ixs.push(ix_trade_ext(prog_id, w_dex, w_mkts[0], wu_pfl, w_user.pubkey(), wk_pfl, w_keep.pubkey(), 2, POS_SCALE / 2, 101_200_000));
    let (cu_handoff_l, wire_handoff_l) = send_ixs_ok_measured(&mut svm, &ho_ixs, &payer, &[&payer, &w_user, &w_keep]);
    assert_eq!(read_u64(&svm, &w_mkts[0], 256), m0_oi_0, "B4 Long->Long handoff must leave oiLong bit-for-bit invariant!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 272), m0_rl_0, "B4 Long->Long handoff must leave rawBasisLong invariant!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 288), m0_adl_0, "B4 Long->Long handoff must leave adlLong invariant!");
    assert_eq!(read_u8(&svm, &wk_pfl, 4), 8, "Keeper now holds ALL 8 LEGS!");
    //   Also test B4 mode=3 (Short->Short handoff on mkt 4 from User A to Aux)!
    let m4_oi_0 = read_u64(&svm, &w_mkts[4], 264);
    let mut ho_s_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wa_pfl, false)).collect();
    ho_s_ixs.push(ix_trade_ext(prog_id, w_dex, w_mkts[4], wu_pfl, w_user.pubkey(), wa_pfl, w_aux.pubkey(), 3, POS_SCALE / 2, 100_200_000));
    let (cu_handoff_s, _) = send_ixs_ok_measured(&mut svm, &ho_s_ixs, &payer, &[&payer, &w_user, &w_aux]);
    assert_eq!(read_u64(&svm, &w_mkts[4], 264), m4_oi_0, "B4 Short->Short handoff must leave oiShort bit-for-bit invariant!");
    assert_dex_invariants(&svm, &w_dex, &w_vault, &w_mkts, &w_all_pfls, "suite11-post-b4-handoff");

    // 11.6 LIQUIDATION KEEPER WORST-CASE (8-LEG VICTIM + 8-LEG LIQUIDATOR + A2 POST-ADL RECOVERY!):
    //   Pump mkts 4..7 (User A is Short) over 19 slots (0.7%/slot) to drain freeCapital near 0
    //   without making mkts 4..7 bankrupt (`shortfall == 0`, honoring #109),
    //   and drop mkt 0 (User A is Long 1.6) 4 slots (-2.8%) so mkt 0 is underwater (`0 < free+lock < legMm`)
    //   and partial liquidation (`reqQty = 0.8`) restores health (`postEq >= remMm`, honoring #107)!
    let mut p0 = 100_700_000u64;
    let mut p_hi = 100_700_000u64;
    for step_idx in 0..19 {
        w_slot += 1;
        set_slot(&mut svm, w_slot);
        p_hi = p_hi + (p_hi * 7) / 1000;
        let mut step_ixs = Vec::new();
        if step_idx < 4 {
            p0 = p0 - (p0 * 7) / 1000;
            step_ixs.push(ix_update_oracle(prog_id, w_mkts[0], w_orc_shared.pubkey(), p0, 0, 0));
        }
        for i in 4..MAX_LEGS {
            step_ixs.push(ix_update_oracle(prog_id, w_mkts[i], w_orc_shared.pubkey(), p_hi, 0, 0));
        }
        send_ixs_ok(&mut svm, &step_ixs, &payer, &[&payer, &w_orc_shared]);
    }
    //   11.6a Worst-Case 8-Leg Tier-3 Fallback Liquidation (`mode = 0`, partial 0.8 on mkt 0 -> triggers partial ADL!)
    //   Atomic ONE-tx: [7x RefreshLeg(wu_pfl, mkts 1..8) + Liquidate(mode=0, reqQty=0.8, mkt 0, wu_pfl)]!
    let mut liq0_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    liq0_ixs.push(ix_liquidate_ext(prog_id, w_dex, w_mkts[0], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID, 0, 800_000, None));
    let (cu_liq8_fallback, wire_liq8_fallback) = send_ixs_ok_measured(&mut svm, &liq0_ixs, &payer, &[&payer]);
    assert!(cu_liq8_fallback < 200_000 && wire_liq8_fallback <= 1232, "8-leg fallback Liquidate exceeded limits: {} CU, {} B", cu_liq8_fallback, wire_liq8_fallback);
    //   Verify partial ADL occurred on mkt 0 (`0 < oiShort < rawBasisShort`, `adlShort < ADL_ONE`)!
    let m0_oi_adl = read_u64(&svm, &w_mkts[0], 264);
    let m0_rs_adl = read_u64(&svm, &w_mkts[0], 280);
    let m0_adls   = read_u64(&svm, &w_mkts[0], 296);
    assert!(m0_oi_adl > 0 && m0_oi_adl < m0_rs_adl && m0_adls < ADL_ONE,
        "Expected partial ADL on mkt 0: oi={}, rawS={}, adlS={}", m0_oi_adl, m0_rs_adl, m0_adls);

    //   11.6a-Gap4B: Asymmetric-ADL Zero-Sum Oracle Settlement Check!
    //   mkt 0 currently has ASYMMETRIC ADL (`oiLong == rawBasisLong`, `oiShort < rawBasisShort`)!
    //   Step price UP (+0.5% -> Shorts lose via ceil `dkLose`, Longs win via floor `dkWin`) AND
    //   confirm `kShort` drop >= `kLong` rise scaled by rawBasis (ZERO under-collection)!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let k_l0 = read_u64(&svm, &w_mkts[0], 304);
    let k_s0 = read_u64(&svm, &w_mkts[0], 312);
    let rl0  = read_u64(&svm, &w_mkts[0], 272) as u128;
    let rs0  = read_u64(&svm, &w_mkts[0], 280) as u128;
    let p0_up = p0 + (p0 * 5) / 1000;
    send_ok(&mut svm, ix_update_oracle(prog_id, w_mkts[0], w_orc_shared.pubkey(), p0_up, 0, 0), &payer, &[&payer, &w_orc_shared]);
    let dk_l = (read_u64(&svm, &w_mkts[0], 304) - k_l0) as u128;
    let dk_s = (k_s0 - read_u64(&svm, &w_mkts[0], 312)) as u128;
    assert!(rs0 * dk_s >= rl0 * dk_l, "Gap #4B violation: asymmetric-ADL losing Shorts under-collected ({} < {})!", rs0 * dk_s, rl0 * dk_l);
    //   Step mkt 0 down so User A's restored 0.8 Long becomes underwater again for 11.6c Takeover!
    let mut p0_cur = p0_up;
    for _ in 0..5 {
        w_slot += 1;
        set_slot(&mut svm, w_slot);
        p0_cur = p0_cur - (p0_cur * 7) / 1000;
        send_ok(&mut svm, ix_update_oracle(prog_id, w_mkts[0], w_orc_shared.pubkey(), p0_cur, 0, 0), &payer, &[&payer, &w_orc_shared]);
    }

    //   11.6b A2 POST-ADL RECOVERY #1: Post-ADL `Trade(mode = 0)` new open on partially-ADL'd mkt 0!
    //   Refresh Aux & Keeper legs, then open 0.5 new OI on partially-ADL'd mkt 0!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut post_adl_open_ixs: Vec<Instruction> = (0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wk_pfl, false)).collect();
    post_adl_open_ixs.extend((1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wa_pfl, false)));
    post_adl_open_ixs.push(ix_trade(prog_id, w_dex, w_mkts[0], wk_pfl, w_keep.pubkey(), wa_pfl, w_aux.pubkey(), 0, 500_000));
    let (cu_post_adl_open, wire_post_adl_open) = send_ixs_ok_measured(&mut svm, &post_adl_open_ixs, &payer, &[&payer, &w_keep, &w_aux]);
    let m0_adls_after_open = read_u64(&svm, &w_mkts[0], 296);
    assert!(m0_adls_after_open <= m0_adls, "A2 post-ADL open must NEVER inflate adlShort ({} > {})!", m0_adls_after_open, m0_adls);
    assert_eq!(read_u64(&svm, &w_mkts[0], 256), m0_oi_adl + 500_000, "A2 post-ADL open increased OI cleanly!");

    //   11.6c A2 POST-ADL RECOVERY #2 + WORST-CASE DOUBLE-8-LEG TAKEOVER (`mode = 1`):
    //   BOTH Victim (wu_pfl, 8 legs) AND Liquidator (wk_pfl, 8 legs!) hold ALL 8 LEGS on a partially-ADL'd market!
    //   Test ONE SINGLE ATOMIC TX: [7x RefreshLeg(wu_pfl) + 7x RefreshLeg(wk_pfl) + Liquidate(mode=1, mkt 0)]!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let m0_oi_pre = read_u64(&svm, &w_mkts[0], 256);
    let m0_rl_pre = read_u64(&svm, &w_mkts[0], 272);
    let m0_rs_pre = read_u64(&svm, &w_mkts[0], 280);
    let m0_adll_pre = read_u64(&svm, &w_mkts[0], 288);
    let m0_adls_pre = read_u64(&svm, &w_mkts[0], 296);
    let mut take16_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    take16_ixs.extend((1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wk_pfl, false)));
    take16_ixs.push(ix_liquidate_ext(prog_id, w_dex, w_mkts[0], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID,
        1, 0, Some((wk_pfl, w_keep.pubkey()))));
    let (cu_liq16_takeover, wire_liq16_takeover) = send_ixs_ok_measured(&mut svm, &take16_ixs, &payer, &[&payer, &w_keep]);
    assert!(cu_liq16_takeover < 200_000 && wire_liq16_takeover <= 1232, "Double-8-leg Takeover exceeded limits: {} CU, {} B", cu_liq16_takeover, wire_liq16_takeover);
    //   Verify Post-ADL Takeover preserved ALL market OI/rawBasis/ADL fields BIT-FOR-BIT!
    assert_eq!(read_u64(&svm, &w_mkts[0], 256), m0_oi_pre, "Post-ADL Takeover must preserve oiLong!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 272), m0_rl_pre, "Post-ADL Takeover must preserve rawBasisLong!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 280), m0_rs_pre, "Post-ADL Takeover must preserve rawBasisShort!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 288), m0_adll_pre, "Post-ADL Takeover must preserve adlLong!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 296), m0_adls_pre, "Post-ADL Takeover must preserve adlShort!");

    // 11.7 CRANK WORST-CASE: Rotate all 8 markets to OracleAdapter CPI & crank all 8 markets via CPI!
    for i in 0..MAX_LEGS {
        send_ok(&mut svm, ix_update_market_auth(prog_id, w_mkts[i], dex_admin.pubkey(), 1, w_orac_pdas[i]), &payer, &[&payer, &dex_admin]);
    }
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut cpi_crank_max_cu = 0u64;
    let mut cpi_crank_total_cu = 0u64;
    for i in 0..MAX_LEGS {
        let cur_p = read_u64(&svm, &w_mkts[i], 112);
        let mut fd = vec![0u8; 32];
        fd[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
        fd[8..16].copy_from_slice(&((cur_p * 1009) / 1000).to_le_bytes());
        fd[16..24].copy_from_slice(&50_000u64.to_le_bytes());
        fd[24..32].copy_from_slice(&w_slot.to_le_bytes());
        svm.set_account(w_feeds[i], Account { lamports: 10_000_000, data: fd, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        let cu = send_ok(
            &mut svm,
            Instruction {
                program_id: adapter_prog,
                accounts: vec![
                    AccountMeta::new_readonly(w_adps[i], false),
                    AccountMeta::new(w_mkts[i], false),
                    AccountMeta::new_readonly(w_feeds[i], false),
                    AccountMeta::new_readonly(w_orac_pdas[i], false),
                    AccountMeta::new_readonly(prog_id, false),
                ],
                data: vec![1],
            },
            &payer,
            &[&payer],
        );
        cpi_crank_max_cu = cpi_crank_max_cu.max(cu);
        cpi_crank_total_cu += cu;
    }

    // 11.8 CRANK WORST-CASE WIND-DOWN SWEEP ACROSS ALL 8 MARKETS:
    //   StartWindDown on all 8 -> advance exitWindow -> ForceClosePair + ClearDeadLeg + ResolveMarket!
    for i in 0..MAX_LEGS {
        send_ok(&mut svm, ix_start_wind_down(prog_id, w_mkts[i], dex_admin.pubkey()), &payer, &[&payer, &dex_admin]);
    }
    w_slot += 15;
    set_slot(&mut svm, w_slot);
    let mut max_fc_cu = 0u64;
    let mut max_res_cu = 0u64;
    for i in 0..MAX_LEGS {
        // Force-close all (Long, Short) pairs among the 4 portfolios until OI == 0
        for _round in 0..6 {
            if read_u64(&svm, &w_mkts[i], 256) == 0 { break; }
            for &p_l in &w_all_pfls {
                for &p_s in &w_all_pfls {
                    if p_l == p_s { continue; }
                    if let Ok(cu) = send_ixs_try(&mut svm, &[ix_force_close_pair(prog_id, w_dex, w_mkts[i], p_l, p_s)], &payer, &[&payer]) {
                        max_fc_cu = max_fc_cu.max(cu);
                    }
                }
            }
        }
        // Clear any remaining post-ADL dead legs on market i
        for &p in &w_all_pfls {
            let _ = send_ixs_try(&mut svm, &[ix_clear_dead_leg(prog_id, w_dex, w_mkts[i], p)], &payer, &[&payer]);
        }
        let cu_res = send_ok(&mut svm, ix_resolve_market(prog_id, w_dex, w_mkts[i]), &payer, &[&payer]);
        max_res_cu = max_res_cu.max(cu_res);
        // Claim any resolved PnL legs
        for &p in &w_all_pfls {
            let _ = send_ixs_try(&mut svm, &[ix_claim_resolved(prog_id, w_dex, w_mkts[i], p)], &payer, &[&payer]);
        }
    }
    assert_dex_invariants(&svm, &w_dex, &w_vault, &w_mkts, &w_all_pfls, "suite11-post-8mkt-resolve");
    println!("[PASS] Suite 11: Worst-Case 8-Leg CU Exhaustion + A1 / A2 / B4 Verified (ZERO CU/MTU Exhaustion!):");
    println!("       User 8-leg Withdraw  [8xRef + Wdr]            : {:>6} CU | {:>4} B / 1232 B (default budget 200k)", cu_user_8wdr, wire_user_8wdr);
    println!("       User 16-leg Trade    [16xRef + Trade]         : {:>6} CU | {:>4} B / 1232 B", cu_user_16trd, wire_user_16trd);
    println!("       B4 Position Hand-Off [7xRef + L->L / S->S]    : {:>6} / {:>5} CU | {:>4} B (OI/ADL bit-for-bit invariant!)", cu_handoff_l, cu_handoff_s, wire_handoff_l);
    println!("       Keeper 8-leg Liq(m0) [7xRef + Fallback]       : {:>6} CU | {:>4} B / 1232 B", cu_liq8_fallback, wire_liq8_fallback);
    println!("       A2 Post-ADL Open     [15xRef + Trade(m0)]     : {:>6} CU | {:>4} B / 1232 B (adl monotone!)", cu_post_adl_open, wire_post_adl_open);
    println!("       Keeper 16-leg Liq(m1)[14xRef + Takeover(ADL)] : {:>6} CU | {:>4} B / 1232 B", cu_liq16_takeover, wire_liq16_takeover);
    println!("       Crank 8-mkt Batch    [8x UpdateOracle 1 tx]   : {:>6} CU | {:>4} B / 1232 B", cu_crank_8orc, wire_8orc);
    println!("       Crank 8-mkt CPI/Sweep[OracleAdapter max/8x]   : {:>6} / {:>5} CU | ForceClose max={} CU, Resolve max={} CU", cpi_crank_max_cu, cpi_crank_total_cu, max_fc_cu, max_res_cu);
    // =========================================================================
    // SUITE 12: 19 Boring Everyday Exchange, Security & Flash-Arb Limit-Order Tests
    // =========================================================================
    let limit_matcher_path = std::env::args()
        .nth(7)
        .unwrap_or_else(|| "build/limit_matcher.so".to_string());
    let limit_matcher_elf = std::fs::read(&limit_matcher_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", limit_matcher_path, e));
    assert_sbpf_v3_elf(&limit_matcher_path, &limit_matcher_elf);
    boring_tests::run_all_boring_tests(&elf, &matcher_elf, &limit_matcher_elf);

    // =========================================================================
    // SUITE 13: Gavel-Style `xy = k` Virtual-Reserve X-Minute Uniform-Price Batch
    //   Buy-and-Burn Reward Modules (8-Leg Cross-Margin User x 8 Unique Modules:
    //   6x SPL Token + Token-2022 + wSOL + Full Mainnet R1-R6 Attack Suite!)
    // =========================================================================
    let reward_so_path = std::env::args()
        .nth(4)
        .unwrap_or_else(|| "build/reward_module.so".to_string());
    let reward_elf = std::fs::read(&reward_so_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", reward_so_path, e));
    let rew_prog = Keypair::new().pubkey();
    svm.add_program(rew_prog, &reward_elf).expect("RewardModule ELF load failed");

    let r_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (r_vault, r_bump) = derive_dex_vault(&prog_id, &r_dex);
    send_ok(
        &mut svm,
        ix_init_dex(prog_id, r_dex, dex_admin.pubkey(), mint, r_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, r_bump, 6, 0, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
    );

    if svm.get_account(&WSOL_MINT).is_none() {
        let mut wsol_mint_data = vec![0u8; 82];
        wsol_mint_data[44] = 9;
        wsol_mint_data[45] = 1;
        svm.set_account(
            WSOL_MINT,
            Account {
                lamports: 10_000_000,
                data: wsol_mint_data,
                owner: TOKEN_PROGRAM_ID,
                executable: false,
                rent_epoch: 0,
            },
        )
        .unwrap();
    }

    let r_trader = Keypair::new();
    let r_mm = Keypair::new();
    let r_bidder_a = Keypair::new();
    let r_bidder_b = Keypair::new();
    let r_spammer = Keypair::new();
    let r_orc = Keypair::new();
    for kp in [&r_trader, &r_mm, &r_bidder_a, &r_bidder_b, &r_spammer, &r_orc] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    let r_trader_tok = create_tok_acc(&mut svm, &mint, &r_trader.pubkey(), 50_000 * POS_SCALE);
    let r_mm_tok = create_tok_acc(&mut svm, &mint, &r_mm.pubkey(), 50_000 * POS_SCALE);
    let r_bidder_a_q = create_tok_acc(&mut svm, &mint, &r_bidder_a.pubkey(), 0);
    let r_bidder_b_q = create_tok_acc(&mut svm, &mint, &r_bidder_b.pubkey(), 0);
    let r_spammer_q = create_tok_acc(&mut svm, &mint, &r_spammer.pubkey(), 0);
    let r_trader_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let r_mm_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, r_dex, r_trader_pfl, r_trader.pubkey()), &payer, &[&payer, &r_trader]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, r_dex, r_mm_pfl, r_mm.pubkey()), &payer, &[&payer, &r_mm]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, r_dex, r_trader_pfl, r_trader.pubkey(), r_trader_tok, mint, r_vault, TOKEN_PROGRAM_ID, 20_000 * POS_SCALE), &payer, &[&payer, &r_trader]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, r_dex, r_mm_pfl, r_mm.pubkey(), r_mm_tok, mint, r_vault, TOKEN_PROGRAM_ID, 20_000 * POS_SCALE), &payer, &[&payer, &r_mm]);

    // 13.1 Negative config checks on CreateMarket reward fields
    let r_bad_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let r_zero_addr = Address::from([0u8; 32]);
    send_err_custom(
        &mut svm,
        ix_create_market_with_reward(prog_id, r_dex, r_bad_mkt, mint, r_orc.pubkey(), r_trader.pubkey(), r_trader_tok, fee_vault,
            100 * POS_SCALE, 10, 500, 0, 1000, 500, 100, 100, 75, 2500, 1_000_000 * POS_SCALE, 0,
            10_001, Keypair::new().pubkey()),
        &payer,
        &[&payer, &r_trader],
        103,
        "CreateMarket rejects rewardBps > 10000",
    );
    send_err_custom(
        &mut svm,
        ix_create_market_with_reward(prog_id, r_dex, r_bad_mkt, mint, r_orc.pubkey(), r_trader.pubkey(), r_trader_tok, fee_vault,
            100 * POS_SCALE, 10, 500, 0, 1000, 500, 100, 100, 75, 2500, 1_000_000 * POS_SCALE, 0,
            5000, r_zero_addr),
        &payer,
        &[&payer, &r_trader],
        103,
        "CreateMarket rejects rewardBps > 0 with zero rewardRecipient",
    );

    // 13.2 Create 8 permissionless markets under ONE DEX, each with its own UNIQUE Gavel `xy=k` Batch RewardModule:
    //   - Markets 0..6: 6 distinct SPL Token mints (burnMode = 0, real SPL Burn reducing supply!)
    //   - Market  6   : Token-2022 mint (burnMode = 0, real Token-2022 Burn reducing supply!)
    //   - Market  7   : wSOL NativeMint (burnMode = 1, permanent dead-sink PDA owned by rewAuthPda!)
    let reward_bps_cfg: [u64; 8] = [5000, 6000, 7000, 8000, 9000, 10000, 7500, 5000];
    let mut r_mkts: Vec<Address> = Vec::with_capacity(8);
    let mut r_cfgs: Vec<Address> = Vec::with_capacity(8);
    let mut r_pdas: Vec<Address> = Vec::with_capacity(8);
    let mut r_q_vaults: Vec<Address> = Vec::with_capacity(8);
    let mut r_t_mints: Vec<Address> = Vec::with_capacity(8);
    let mut r_t_escrows: Vec<Address> = Vec::with_capacity(8);
    let mut r_t_progs: Vec<Address> = Vec::with_capacity(8);
    let mut r_bida_t: Vec<Address> = Vec::with_capacity(8);
    let mut r_bidb_t: Vec<Address> = Vec::with_capacity(8);
    let mut r_spam_t: Vec<Address> = Vec::with_capacity(8);
    let mut r_sinks: Vec<Option<Address>> = Vec::with_capacity(8);

    let r_slot_start = get_slot(&svm) + 10;
    set_slot(&mut svm, r_slot_start);
    let epoch_slots = 150u64; // ~1 min (>= MIN_EPOCH_SLOTS = 32 >> K = 4 leader window!)
    let min_batch_quote = 1_000_000u64; // $1 minimum batch
    let init_reserve_rate_e6 = 500_000u64; // 0.5 target-atoms per 1 quote-atom virtual reserve

    for i in 0..MAX_LEGS {
        let creator = Keypair::new();
        svm.airdrop(&creator.pubkey(), 1_000_000_000).unwrap();
        let creator_tok = create_tok_acc(&mut svm, &mint, &creator.pubkey(), 0);

        let mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let cfg = create_prog_acc(&mut svm, &rew_prog, REW_SIZE);
        let (rew_pda, pda_bump) = derive_rew_auth(&rew_prog, &cfg);
        let q_vault = create_tok_acc(&mut svm, &mint, &rew_pda, 0);

        send_ok(
            &mut svm,
            ix_create_market_with_reward(
                prog_id, r_dex, mkt, mint, r_orc.pubkey(), creator.pubkey(), creator_tok, fee_vault,
                100 * POS_SCALE, 10, 2000, 0, 1000, 500, 100, 100, 75, 2500, 1_000_000 * POS_SCALE, 0,
                reward_bps_cfg[i], rew_pda,
            ),
            &payer,
            &[&payer, &creator],
        );

        let (t_mint, t_prog, burn_mode, t_escrow, sink_opt, ba_tok, bb_tok, sp_tok) = if i < 6 {
            let tm = Keypair::new().pubkey();
            svm.set_account(
                tm,
                Account {
                    lamports: 10_000_000,
                    data: make_spl_mint(6, 1_000_000_000_000, &dex_admin.pubkey()),
                    owner: TOKEN_PROGRAM_ID,
                    executable: false,
                    rent_epoch: 0,
                },
            )
            .unwrap();
            let esc = create_tok_acc_prog(&mut svm, TOKEN_PROGRAM_ID, &tm, &rew_pda, 0);
            let ba = create_tok_acc_prog(&mut svm, TOKEN_PROGRAM_ID, &tm, &r_bidder_a.pubkey(), 50_000 * POS_SCALE);
            let bb = create_tok_acc_prog(&mut svm, TOKEN_PROGRAM_ID, &tm, &r_bidder_b.pubkey(), 50_000 * POS_SCALE);
            let sp = create_tok_acc_prog(&mut svm, TOKEN_PROGRAM_ID, &tm, &r_spammer.pubkey(), 50_000 * POS_SCALE);
            (tm, TOKEN_PROGRAM_ID, 0u8, esc, None, ba, bb, sp)
        } else if i == 6 {
            let tm = Keypair::new().pubkey();
            svm.set_account(
                tm,
                Account {
                    lamports: 10_000_000,
                    data: make_spl_mint(6, 1_000_000_000_000, &dex_admin.pubkey()),
                    owner: TOKEN_2022_PROGRAM_ID,
                    executable: false,
                    rent_epoch: 0,
                },
            )
            .unwrap();
            let esc = create_tok_acc_prog(&mut svm, TOKEN_2022_PROGRAM_ID, &tm, &rew_pda, 0);
            let ba = create_tok_acc_prog(&mut svm, TOKEN_2022_PROGRAM_ID, &tm, &r_bidder_a.pubkey(), 50_000 * POS_SCALE);
            let bb = create_tok_acc_prog(&mut svm, TOKEN_2022_PROGRAM_ID, &tm, &r_bidder_b.pubkey(), 50_000 * POS_SCALE);
            let sp = create_tok_acc_prog(&mut svm, TOKEN_2022_PROGRAM_ID, &tm, &r_spammer.pubkey(), 50_000 * POS_SCALE);
            (tm, TOKEN_2022_PROGRAM_ID, 0u8, esc, None, ba, bb, sp)
        } else {
            let esc = create_wsol_acc(&mut svm, &rew_pda, 0);
            let sink = create_wsol_acc(&mut svm, &rew_pda, 0);
            let ba = create_wsol_acc(&mut svm, &r_bidder_a.pubkey(), 50_000 * POS_SCALE);
            let bb = create_wsol_acc(&mut svm, &r_bidder_b.pubkey(), 50_000 * POS_SCALE);
            let sp = create_wsol_acc(&mut svm, &r_spammer.pubkey(), 50_000 * POS_SCALE);
            (WSOL_MINT, TOKEN_PROGRAM_ID, 1u8, esc, Some(sink), ba, bb, sp)
        };

        // Security regressions on Market 0 before valid InitReward:
        if i == 0 {
            send_err_custom(
                &mut svm,
                ix_init_reward(rew_prog, cfg, attacker.pubkey(), prog_id, r_dex, mkt, rew_pda,
                    mint, q_vault, TOKEN_PROGRAM_ID, t_mint, t_escrow, t_prog, sink_opt,
                    pda_bump, burn_mode, epoch_slots, min_batch_quote, init_reserve_rate_e6),
                &payer, &[&payer, &attacker], 102, "InitReward rejects non-marketAdmin hijack",
            );
            send_err(
                &mut svm,
                ix_init_reward(rew_prog, cfg, creator.pubkey(), prog_id, r_dex, mkt, rew_pda,
                    mint, q_vault, TOKEN_PROGRAM_ID, t_mint, t_escrow, fake_tok_prog, sink_opt,
                    pda_bump, burn_mode, epoch_slots, min_batch_quote, init_reserve_rate_e6),
                &payer, &[&payer, &creator], "InitReward rejects spoofed noop.so targetTokProg",
            );
            send_err_custom(
                &mut svm,
                ix_init_reward(rew_prog, cfg, creator.pubkey(), prog_id, r_dex, mkt, Keypair::new().pubkey(),
                    mint, q_vault, TOKEN_PROGRAM_ID, t_mint, t_escrow, t_prog, sink_opt,
                    pda_bump, burn_mode, epoch_slots, min_batch_quote, init_reserve_rate_e6),
                &payer, &[&payer, &creator], 407, "InitReward rejects mismatched rewAuthPda",
            );
            send_err_custom(
                &mut svm,
                ix_init_reward(rew_prog, cfg, creator.pubkey(), prog_id, r_dex, mkt, rew_pda,
                    mint, q_vault, TOKEN_PROGRAM_ID, t_mint, t_escrow, t_prog, sink_opt,
                    pda_bump, burn_mode, 4, min_batch_quote, init_reserve_rate_e6), // 4 < MIN_EPOCH_SLOTS (32)!
                &payer, &[&payer, &creator], 103, "InitReward rejects epochSlots < MIN_EPOCH_SLOTS",
            );
        }

        send_ok(
            &mut svm,
            ix_init_reward(rew_prog, cfg, creator.pubkey(), prog_id, r_dex, mkt, rew_pda,
                mint, q_vault, TOKEN_PROGRAM_ID, t_mint, t_escrow, t_prog, sink_opt,
                pda_bump, burn_mode, epoch_slots, min_batch_quote, init_reserve_rate_e6),
            &payer,
            &[&payer, &creator],
        );

        r_mkts.push(mkt);
        r_cfgs.push(cfg);
        r_pdas.push(rew_pda);
        r_q_vaults.push(q_vault);
        r_t_mints.push(t_mint);
        r_t_escrows.push(t_escrow);
        r_t_progs.push(t_prog);
        r_bida_t.push(ba_tok);
        r_bidb_t.push(bb_tok);
        r_spam_t.push(sp_tok);
        r_sinks.push(sink_opt);
    }

    // 13.3 Single user opens ALL 8 CROSS-MARGIN LEGS across ALL 8 markets with 8 unique reward modules!
    let mut expected_rew: [u64; 8] = [0; 8];
    let mut expected_ins: [u64; 8] = [0; 8];
    let mut total_expected_rew = 0u64;
    for i in 0..MAX_LEGS {
        let trade_ix = if i % 2 == 0 {
            ix_trade(prog_id, r_dex, r_mkts[i], r_trader_pfl, r_trader.pubkey(), r_mm_pfl, r_mm.pubkey(), 0, 10 * POS_SCALE)
        } else {
            ix_trade(prog_id, r_dex, r_mkts[i], r_mm_pfl, r_mm.pubkey(), r_trader_pfl, r_trader.pubkey(), 0, 10 * POS_SCALE)
        };
        send_ok(&mut svm, trade_ix, &payer, &[&payer, &r_trader, &r_mm]);
        let fee2 = 20 * POS_SCALE;
        let rew_fee = (fee2 * reward_bps_cfg[i]) / 10_000;
        let ins_fee = fee2 - rew_fee;
        expected_rew[i] = rew_fee;
        expected_ins[i] = ins_fee;
        total_expected_rew += rew_fee;
        assert_eq!(read_u64(&svm, &r_mkts[i], 360), rew_fee, "Market {} rewardAccrued mismatch", i);
        assert_eq!(read_u64(&svm, &r_mkts[i], 224), ins_fee, "Market {} insurance split mismatch", i);
    }
    assert_eq!(read_u8(&svm, &r_trader_pfl, 4), 8, "Single user holds ALL 8 cross-margin legs!");
    assert_eq!(read_u64(&svm, &r_dex, 200), total_expected_rew, "Dex.totalRewards mismatch!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl], "suite13-post-8leg-open");

    // 13.4 Core isolation checks: dexAdmin SweepSurplus cannot touch totalRewards; unauthorized ClaimReward rejected!
    send_err_custom(
        &mut svm,
        ix_sweep_surplus(prog_id, r_dex, dex_admin.pubkey(), mint, r_vault, fee_vault, TOKEN_PROGRAM_ID, 0),
        &payer, &[&payer, &dex_admin], 103, "dexAdmin SweepSurplus must NEVER steal totalRewards!",
    );
    send_err_custom(
        &mut svm,
        ix_claim_reward(prog_id, r_dex, r_mkts[0], attacker.pubkey(), mint, r_vault, attacker_tok, TOKEN_PROGRAM_ID, 0),
        &payer, &[&payer, &attacker], 102, "ClaimReward rejects unauthorized signer!",
    );

    // 13.5 Start Epoch 1 on ALL 8 markets (pulls m.rewardAccrued -> quoteVault, computes B_virt = Q * 0.5)
    let mut r_ep1: Vec<Address> = Vec::with_capacity(8);
    let trader_cap_pre = read_u64(&svm, &r_trader_pfl, 88);
    let mm_cap_pre = read_u64(&svm, &r_mm_pfl, 88);
    for i in 0..MAX_LEGS {
        let ep1 = create_prog_acc(&mut svm, &rew_prog, EPOCH_SIZE);
        send_ok(
            &mut svm,
            ix_start_epoch(rew_prog, r_cfgs[i], ep1, r_dex, r_mkts[i], r_pdas[i], mint, r_vault, r_q_vaults[i], TOKEN_PROGRAM_ID, prog_id),
            &payer, &[&payer],
        );
        assert_eq!(read_u64(&svm, &r_mkts[i], 360), 0, "Mkt {} rewardAccrued pulled into Epoch 1", i);
        assert_eq!(token_amount(&svm, &r_q_vaults[i]), expected_rew[i], "Mkt {} quoteVault funded", i);
        assert_eq!(read_u64(&svm, &ep1, 48), expected_rew[i], "Epoch 1 quotePot");
        assert_eq!(read_u64(&svm, &ep1, 56), expected_rew[i] / 2, "Epoch 1 virtBids = Q * 0.5");
        r_ep1.push(ep1);
    }
    assert_eq!(read_u64(&svm, &r_dex, 200), 0, "All 8 markets' rewards pulled cleanly!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl], "suite13-post-start-ep1");

    // 13.6 Unlimited AMM-Style Bidding + R1/R4 Spam Bid Attack + R5 Quiet-Epoch 1-Atom Snipe!
    //   - Market 0 (SPL): bidder_a bids 4*POS_SCALE + 6*POS_SCALE across TWO calls (same receipt!),
    //     bidder_b bids 30*POS_SCALE, AND spammer drops FIVE 1-atom dust bids across 5 separate receipts!
    //   - Market 1 (SPL): QUIET / CENSORED EPOCH TEST (R5/R3): ONLY spammer drops a 1-atom bid!
    //   - Markets 2..5 (SPL), Market 6 (Token-2022), Market 7 (wSOL): bidder_a + bidder_b both bid!
    let mut rec_a: Vec<Option<Address>> = vec![None; 8];
    let mut rec_b: Vec<Option<Address>> = vec![None; 8];
    let mut spam_recs_m0: Vec<Address> = Vec::new();
    let mut spam_rec_m1 = Address::default();

    for i in 0..MAX_LEGS {
        if i == 1 {
            // Quiet/censored epoch: ONLY 1-atom attacker bid!
            spam_rec_m1 = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
            send_ok(
                &mut svm,
                ix_submit_bid(rew_prog, r_cfgs[1], r_ep1[1], spam_rec_m1, r_spammer.pubkey(), r_spam_t[1], r_t_escrows[1], r_t_mints[1], r_t_progs[1], 1),
                &payer, &[&payer, &r_spammer],
            );
        } else {
            let ra = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
            let rb = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
            if i == 0 {
                // Multi-bid accumulation into the same receipt (4 + 6 = 10)
                send_ok(&mut svm, ix_submit_bid(rew_prog, r_cfgs[0], r_ep1[0], ra, r_bidder_a.pubkey(), r_bida_t[0], r_t_escrows[0], r_t_mints[0], r_t_progs[0], 4 * POS_SCALE), &payer, &[&payer, &r_bidder_a]);
                send_ok(&mut svm, ix_submit_bid(rew_prog, r_cfgs[0], r_ep1[0], ra, r_bidder_a.pubkey(), r_bida_t[0], r_t_escrows[0], r_t_mints[0], r_t_progs[0], 6 * POS_SCALE), &payer, &[&payer, &r_bidder_a]);
                send_ok(&mut svm, ix_submit_bid(rew_prog, r_cfgs[0], r_ep1[0], rb, r_bidder_b.pubkey(), r_bidb_t[0], r_t_escrows[0], r_t_mints[0], r_t_progs[0], 30 * POS_SCALE), &payer, &[&payer, &r_bidder_b]);
                // 5 dust 1-atom spam bids across 5 separate receipts (R1/R4 spam test!)
                for _ in 0..5 {
                    let sr = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
                    send_ok(&mut svm, ix_submit_bid(rew_prog, r_cfgs[0], r_ep1[0], sr, r_spammer.pubkey(), r_spam_t[0], r_t_escrows[0], r_t_mints[0], r_t_progs[0], 1), &payer, &[&payer, &r_spammer]);
                    spam_recs_m0.push(sr);
                }
            } else {
                send_ok(&mut svm, ix_submit_bid(rew_prog, r_cfgs[i], r_ep1[i], ra, r_bidder_a.pubkey(), r_bida_t[i], r_t_escrows[i], r_t_mints[i], r_t_progs[i], 10 * POS_SCALE), &payer, &[&payer, &r_bidder_a]);
                send_ok(&mut svm, ix_submit_bid(rew_prog, r_cfgs[i], r_ep1[i], rb, r_bidder_b.pubkey(), r_bidb_t[i], r_t_escrows[i], r_t_mints[i], r_t_progs[i], 30 * POS_SCALE), &payer, &[&payer, &r_bidder_b]);
            }
            rec_a[i] = Some(ra);
            rec_b[i] = Some(rb);
        }
    }

    // Cannot settle BEFORE endSlot!
    send_err_custom(
        &mut svm,
        ix_settle_epoch(rew_prog, r_cfgs[0], r_ep1[0], r_pdas[0], r_t_escrows[0], r_t_mints[0], r_t_progs[0], r_sinks[0]),
        &payer, &[&payer], 410, "SettleEpoch rejects before endSlot",
    );

    // 13.7 Advance to X-minute mark (`r_slot_start + epoch_slots`)!
    set_slot(&mut svm, r_slot_start + epoch_slots);
    // Late bid after endSlot MUST be rejected!
    let late_rec = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
    send_err_custom(
        &mut svm,
        ix_submit_bid(rew_prog, r_cfgs[0], r_ep1[0], late_rec, r_bidder_a.pubkey(), r_bida_t[0], r_t_escrows[0], r_t_mints[0], r_t_progs[0], POS_SCALE),
        &payer, &[&payer, &r_bidder_a], 409, "SubmitBid rejects after endSlot",
    );

    // O(1) SettleEpoch on ALL 8 unique reward modules (6x SPL Burn, 1x Token-2022 Burn, 1x wSOL Dead-Sink)!
    let mut max_settle_cu = 0u64;
    let mut max_claim_cu = 0u64;
    for i in 0..MAX_LEGS {
        let supply_pre = if i < 7 { mint_supply(&svm, &r_t_mints[i]) } else { 0 };
        let sink_pre = r_sinks[i].map(|s| token_amount(&svm, &s)).unwrap_or(0);
        let q_pot = read_u64(&svm, &r_ep1[i], 48);
        let b_virt = read_u64(&svm, &r_ep1[i], 56);
        let tot_b = read_u64(&svm, &r_ep1[i], 64);

        let cu_s = send_ok(
            &mut svm,
            ix_settle_epoch(rew_prog, r_cfgs[i], r_ep1[i], r_pdas[i], r_t_escrows[i], r_t_mints[i], r_t_progs[i], r_sinks[i]),
            &payer, &[&payer],
        );
        max_settle_cu = max_settle_cu.max(cu_s);

        let expected_q_paid = ((q_pot as u128 * tot_b as u128) / (tot_b as u128 + b_virt as u128)) as u64;
        let expected_roll = q_pot - expected_q_paid;
        assert_eq!(read_u64(&svm, &r_ep1[i], 72), expected_q_paid, "Mkt {} quotePaid exact xy=k mismatch", i);
        assert_eq!(read_u64(&svm, &r_cfgs[i], 368), expected_roll, "Mkt {} rolloverQuote mismatch", i);
        assert_eq!(read_u64(&svm, &r_cfgs[i], 392), tot_b, "Mkt {} totalTargetBurned mismatch", i);
        assert_eq!(token_amount(&svm, &r_t_escrows[i]), 0, "Mkt {} targetEscrow completely burned/drained!", i);

        if i < 7 {
            assert_eq!(supply_pre - mint_supply(&svm, &r_t_mints[i]), tot_b, "Mkt {} SPL/Token-2022 mint.supply decreased by exact tot_b!", i);
        } else {
            assert_eq!(token_amount(&svm, &r_sinks[i].unwrap()) - sink_pre, tot_b, "Mkt 7 wSOL dead-sink received exact tot_b!");
        }

        if i == 1 {
            // R5 QUIET/CENSORED EPOCH VERIFICATION (Theorem 4: `payout * B_virt <= Q * b`):
            //   With `reserveRateE6 = 0.5`, 1 target-atom buys at most `floor(Q / (1 + Q/2)) = 1`
            //   quote atom (0.00002% of pot!), >99.9999% rolls over intact, AND `reserveRateE6` halves (500k -> 250k)!
            assert!((expected_q_paid as u128) * (b_virt as u128) <= (q_pot as u128), "R5: quiet_epoch_price_cap violated!");
            assert!(expected_q_paid <= 2, "R5: 1-atom bidder in quiet epoch extracted {} > 2 atoms!", expected_q_paid);
            assert_eq!(read_u64(&svm, &r_cfgs[1], 368), expected_roll, "R5: quiet epoch pot rolled over intact!");
            assert_eq!(read_u64(&svm, &r_cfgs[1], 344), init_reserve_rate_e6 / 2, "R3: under-filled epoch halved reserveRateE6!");

            // Claiming the 1-atom spam receipt yields at most `expected_q_paid` (1 micro-USDC); Epoch 2 starts IMMEDIATELY!
            let sp_pre = token_amount(&svm, &r_spammer_q);
            send_ok(&mut svm, ix_claim_quote(rew_prog, r_cfgs[1], r_ep1[1], spam_rec_m1, r_spammer.pubkey(), r_pdas[1], r_q_vaults[1], r_spammer_q, mint, TOKEN_PROGRAM_ID), &payer, &[&payer, &r_spammer]);
            assert_eq!(token_amount(&svm, &r_spammer_q) - sp_pre, expected_q_paid, "R5: 1-atom attacker payout exact!");

            // Overlapping Epoch 2 starts IMMEDIATELY from rolloverQuote with halved reserveRateE6!
            let ep2 = create_prog_acc(&mut svm, &rew_prog, EPOCH_SIZE);
            send_ok(&mut svm, ix_start_epoch(rew_prog, r_cfgs[1], ep2, r_dex, r_mkts[1], r_pdas[1], mint, r_vault, r_q_vaults[1], TOKEN_PROGRAM_ID, prog_id), &payer, &[&payer]);
            assert_eq!(read_u64(&svm, &ep2, 48), expected_roll, "Epoch 2 carries 100% of rolled-over quote!");
            let exp_virt2 = ((expected_roll as u128 * (init_reserve_rate_e6 / 2) as u128 + 999_999) / 1_000_000) as u64;
            assert_eq!(read_u64(&svm, &ep2, 56), exp_virt2, "Epoch 2 virtBids reflects ceil(rollover * 0.25)!");
        } else {
            // Healthy epoch: bidder_a (10) & bidder_b (30) claim at EXACT uniform xy=k price AND reclaim BidReceipt rent!
            let qa_pre = token_amount(&svm, &r_bidder_a_q);
            let qb_pre = token_amount(&svm, &r_bidder_b_q);
            let lam_a_pre = svm.get_account(&r_bidder_a.pubkey()).unwrap().lamports;
            let lam_rec_a = svm.get_account(&rec_a[i].unwrap()).unwrap().lamports;
            let lam_b_pre = svm.get_account(&r_bidder_b.pubkey()).unwrap().lamports;
            let lam_rec_b = svm.get_account(&rec_b[i].unwrap()).unwrap().lamports;
            let cu_ca = send_ok(&mut svm, ix_claim_quote(rew_prog, r_cfgs[i], r_ep1[i], rec_a[i].unwrap(), r_bidder_a.pubkey(), r_pdas[i], r_q_vaults[i], r_bidder_a_q, mint, TOKEN_PROGRAM_ID), &payer, &[&payer, &r_bidder_a]);
            let cu_cb = send_ok(&mut svm, ix_claim_quote(rew_prog, r_cfgs[i], r_ep1[i], rec_b[i].unwrap(), r_bidder_b.pubkey(), r_pdas[i], r_q_vaults[i], r_bidder_b_q, mint, TOKEN_PROGRAM_ID), &payer, &[&payer, &r_bidder_b]);
            max_claim_cu = max_claim_cu.max(cu_ca).max(cu_cb);
            assert_eq!(svm.get_account(&r_bidder_a.pubkey()).unwrap().lamports, lam_a_pre + lam_rec_a, "Mkt {} ClaimQuote refunded 100% of BidReceipt rent to bidder_a!", i);
            assert_eq!(svm.get_account(&r_bidder_b.pubkey()).unwrap().lamports, lam_b_pre + lam_rec_b, "Mkt {} ClaimQuote refunded 100% of BidReceipt rent to bidder_b!", i);
            let got_a = token_amount(&svm, &r_bidder_a_q) - qa_pre;
            let got_b = token_amount(&svm, &r_bidder_b_q) - qb_pre;
            let exp_a = ((q_pot as u128 * (10 * POS_SCALE) as u128) / (tot_b as u128 + b_virt as u128)) as u64;
            let exp_b = ((q_pot as u128 * (30 * POS_SCALE) as u128) / (tot_b as u128 + b_virt as u128)) as u64;
            assert_eq!(got_a, exp_a, "Mkt {} bidder_a uniform xy=k payout mismatch", i);
            assert_eq!(got_b, exp_b, "Mkt {} bidder_b uniform xy=k payout mismatch", i);
            // Uniform clearing price check: bidder_b bid 3x bidder_a -> receives exact 3x payout (within 1 atom floor)!
            assert!(got_b.abs_diff(3 * got_a) <= 3, "Uniform clearing price violated: got_a={}, got_b={}", got_a, got_b);

            if i == 0 {
                // Double-claim rejected (closed BidReceipt cannot be re-claimed)!
                send_err(
                    &mut svm,
                    ix_claim_quote(rew_prog, r_cfgs[0], r_ep1[0], rec_a[0].unwrap(), r_bidder_a.pubkey(), r_pdas[0], r_q_vaults[0], r_bidder_a_q, mint, TOKEN_PROGRAM_ID),
                    &payer, &[&payer, &r_bidder_a], "Double ClaimQuote on auto-closed receipt rejected",
                );
                // All 5 1-atom spam receipts receive 0 USDC AND auto-close cleanly!
                let sp_pre = token_amount(&svm, &r_spammer_q);
                for sr in &spam_recs_m0 {
                    send_ok(&mut svm, ix_claim_quote(rew_prog, r_cfgs[0], r_ep1[0], *sr, r_spammer.pubkey(), r_pdas[0], r_q_vaults[0], r_spammer_q, mint, TOKEN_PROGRAM_ID), &payer, &[&payer, &r_spammer]);
                }
                assert_eq!(token_amount(&svm, &r_spammer_q), sp_pre, "R1/R4: 5x 1-atom spam bids received 0 USDC & donated to burn!");
            }
        }

        // Verify 3-bucket escrow conservation on RewardCfg: quoteVault >= active + rollover + pending!
        let qv_bal = token_amount(&svm, &r_q_vaults[i]);
        let act_q = read_u64(&svm, &r_cfgs[i], 360);
        let rol_q = read_u64(&svm, &r_cfgs[i], 368);
        let pnd_q = read_u64(&svm, &r_cfgs[i], 376);
        assert!(qv_bal >= act_q + rol_q + pnd_q, "Mkt {} RewardCfg escrow insolvent: {} < {}+{}+{}", i, qv_bal, act_q, rol_q, pnd_q);

        // Cross-market isolation: EVERY market's insurance pool untouched!
        for j in 0..MAX_LEGS {
            assert_eq!(read_u64(&svm, &r_mkts[j], 224), expected_ins[j], "Settle/Claim({}) modified Market {} insurance!", i, j);
        }
    }
    // 13.8 Small-pot `virtBids` ceil regression (`totalPot * resRate < 1_000_000` -> `virtBids == 1 > 0`!):
    //      Pre-fix floor rounded `virtBids = 0` so a 1-atom bidder drained 100% of `totalPot`!
    //      With `mulDiv64Ceil`, `virtBids == 1`, so 1-atom bidder gets at most `floor(100 * 1 / 2) = 50`!
    {
        let sp_creator = Keypair::new();
        svm.airdrop(&sp_creator.pubkey(), 1_000_000_000).unwrap();
        let sp_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let sp_cfg = create_prog_acc(&mut svm, &rew_prog, REW_SIZE);
        let (sp_pda, sp_bump) = Address::find_program_address(&[b"rewm", sp_cfg.as_ref()], &rew_prog);
        let sp_q_vault = create_tok_acc(&mut svm, &mint, &sp_pda, 0);
        let sp_t_mint = Keypair::new().pubkey();
        svm.set_account(sp_t_mint, Account { lamports: 10_000_000, data: make_spl_mint(6, 1_000_000, &payer.pubkey()), owner: TOKEN_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        let sp_t_escrow = create_tok_acc(&mut svm, &sp_t_mint, &sp_pda, 0);
        let sp_bidder_t = create_tok_acc(&mut svm, &sp_t_mint, &r_spammer.pubkey(), 100);
        let sp_creator_tok = create_tok_acc(&mut svm, &mint, &sp_creator.pubkey(), 0);
        send_ok(&mut svm, ix_create_market_with_reward(
            prog_id, r_dex, sp_mkt, mint, r_orc.pubkey(), sp_creator.pubkey(), sp_creator_tok, fee_vault,
            100 * POS_SCALE, 10, 500, 0, 1000, 500, 100, 10, 75, 2500, 1_000_000 * POS_SCALE, 0, 10_000, sp_pda,
        ), &payer, &[&payer, &sp_creator]);
        // minBatchQuote = 100, initReserveRateE6 = 1 -> product = 100 < 1_000_000!
        send_ok(&mut svm, ix_init_reward(
            rew_prog, sp_cfg, sp_creator.pubkey(), prog_id, r_dex, sp_mkt, sp_pda,
            mint, sp_q_vault, TOKEN_PROGRAM_ID, sp_t_mint, sp_t_escrow, TOKEN_PROGRAM_ID, None,
            sp_bump, 0, 32, 100, 1,
        ), &payer, &[&payer, &sp_creator]);
        // Accrue exact 200 micro-USDC trade fee (`qty = 1_000` @ $100 -> notional = 100_000 -> 10 bps fee = 100 each -> fee2 = 200)
        let sp_l = Keypair::new(); let sp_s = Keypair::new();
        svm.airdrop(&sp_l.pubkey(), 1_000_000_000).unwrap(); svm.airdrop(&sp_s.pubkey(), 1_000_000_000).unwrap();
        let sp_lt = create_tok_acc(&mut svm, &mint, &sp_l.pubkey(), 10 * POS_SCALE);
        let sp_st = create_tok_acc(&mut svm, &mint, &sp_s.pubkey(), 10 * POS_SCALE);
        let sp_lp = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let sp_sp = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        send_ok(&mut svm, ix_init_portfolio(prog_id, r_dex, sp_lp, sp_l.pubkey()), &payer, &[&payer, &sp_l]);
        send_ok(&mut svm, ix_init_portfolio(prog_id, r_dex, sp_sp, sp_s.pubkey()), &payer, &[&payer, &sp_s]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, r_dex, sp_lp, sp_l.pubkey(), sp_lt, mint, r_vault, TOKEN_PROGRAM_ID, POS_SCALE), &payer, &[&payer, &sp_l]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, r_dex, sp_sp, sp_s.pubkey(), sp_st, mint, r_vault, TOKEN_PROGRAM_ID, POS_SCALE), &payer, &[&payer, &sp_s]);
        send_ok(&mut svm, ix_trade(prog_id, r_dex, sp_mkt, sp_lp, sp_l.pubkey(), sp_sp, sp_s.pubkey(), 0, 1_000), &payer, &[&payer, &sp_l, &sp_s]);
        let accrued = read_u64(&svm, &sp_mkt, 360);
        assert_eq!(accrued, 200, "Small-pot accrued exactly 200 micro-USDC (< 1_000_000)");
        let sp_ep = create_prog_acc(&mut svm, &rew_prog, EPOCH_SIZE);
        send_ok(&mut svm, ix_start_epoch(rew_prog, sp_cfg, sp_ep, r_dex, sp_mkt, sp_pda, mint, r_vault, sp_q_vault, TOKEN_PROGRAM_ID, prog_id), &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &sp_ep, 56), 1, "virtBids MUST ceil to 1 (never 0!) when totalPot * resRate < 1e6!");
        let sp_rec = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
        send_ok(&mut svm, ix_submit_bid(rew_prog, sp_cfg, sp_ep, sp_rec, r_spammer.pubkey(), sp_bidder_t, sp_t_escrow, sp_t_mint, TOKEN_PROGRAM_ID, 1), &payer, &[&payer, &r_spammer]);
        let sp_end = get_slot(&svm) + 32;
        set_slot(&mut svm, sp_end);
        send_ok(&mut svm, ix_settle_epoch(rew_prog, sp_cfg, sp_ep, sp_pda, sp_t_escrow, sp_t_mint, TOKEN_PROGRAM_ID, None), &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &sp_ep, 72), 100, "1-atom bidder got floor(200*1/2)=100 (NOT 100% drain of 200)!");
        assert_eq!(read_u64(&svm, &sp_cfg, 368), 100, "Remaining 50% rolled over safely!");
        // Clean up temporary small-pot portfolios so r_dex invariants stay exact for Suite 13 & 14!
        send_ok(&mut svm, ix_trade(prog_id, r_dex, sp_mkt, sp_lp, sp_l.pubkey(), sp_sp, sp_s.pubkey(), 1, 1_000), &payer, &[&payer, &sp_l, &sp_s]);
        send_ok(&mut svm, ix_withdraw_collateral(prog_id, r_dex, sp_lp, sp_l.pubkey(), sp_lt, mint, r_vault, TOKEN_PROGRAM_ID, POS_SCALE - 100), &payer, &[&payer, &sp_l]);
        send_ok(&mut svm, ix_withdraw_collateral(prog_id, r_dex, sp_sp, sp_s.pubkey(), sp_st, mint, r_vault, TOKEN_PROGRAM_ID, POS_SCALE - 100), &payer, &[&payer, &sp_s]);
    }

    assert_eq!(read_u64(&svm, &r_trader_pfl, 88), trader_cap_pre, "User capital untouched!");
    assert_eq!(read_u64(&svm, &r_mm_pfl, 88), mm_cap_pre, "MM capital untouched!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl], "suite13-final");
    println!("[PASS] Suite 13: Gavel xy=k X-Min Uniform-Price Batch Reward Modules (8-Leg User x 8 Unique Modules: 6x SPL + Token-2022 + wSOL, R1-R6 Verified, settle max={} CU, claim max={} CU)", max_settle_cu, max_claim_cu);

    // =========================================================================
    // SUITE 14: Legacy-Percolator CPI-Out Adversarial PropAMM (`TradeWithMatcher`)
    //   ZERO taker signer delegation! LP retains 100% EOA custody over withdrawals!
    //   Tests BOTH honest external PropAMM (`matcher.so` Op 4/5) AND all 11 adversarial
    //   exploit vectors using `evil_matcher.so` & `noop.so`:
    //     1) Unbound LP rejected (`Custom(131)`)
    //     2) Mismatched `matcherCtx` rejected (`Custom(131)`)
    //     3) Self-CPI (`matcherProg == percProg`) rejected (`Custom(131)`)
    //     4) Over-fill (`fillQty = maxQty + 1`) rejected (`Custom(131)`)
    //     5) Abusive price violating taker `limitPrice` rejected (`Custom(130)`)
    //     6) Nonzero `status` rejected (`Custom(131)`)
    //     7) `noop.so` / stale `seq` replay rejected (`Custom(131)`)
    //     8) Corrupt return magic rejected (`Custom(131)`)
    //     9) Zero fill (`fillQty = 0`) rejected (`Custom(131)`)
    //    10) Exceeds core `maxMoveBps` clamp with `limitPrice = 0` rejected (`Custom(130)`)
    //    11) Tampering with readonly `extraAcc` rejected by Agave VM write-protection!
    //    12) LP revokes `SetPortfolioMatcher(None)` & withdraws 100% EOA collateral!
    // =========================================================================
    let evil_path = std::env::args()
        .nth(5)
        .unwrap_or_else(|| "build/evil_matcher.so".to_string());
    let evil_elf = std::fs::read(&evil_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", evil_path, e));
    let evil_prog = Keypair::new().pubkey();
    svm.add_program(evil_prog, &evil_elf).expect("evil_matcher ELF load failed");

    let prop_lp_kp = Keypair::new();
    let prop_taker_kp = Keypair::new();
    svm.airdrop(&prop_lp_kp.pubkey(), 1_000_000_000).unwrap();
    svm.airdrop(&prop_taker_kp.pubkey(), 1_000_000_000).unwrap();
    let prop_lp_tok = create_tok_acc(&mut svm, &mint, &prop_lp_kp.pubkey(), 5_000 * POS_SCALE);
    let prop_taker_tok = create_tok_acc(&mut svm, &mint, &prop_taker_kp.pubkey(), 5_000 * POS_SCALE);

    let prop_lp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let prop_taker_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, r_dex, prop_lp_pfl, prop_lp_kp.pubkey()), &payer, &[&payer, &prop_lp_kp]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey()), &payer, &[&payer, &prop_taker_kp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, r_dex, prop_lp_pfl, prop_lp_kp.pubkey(), prop_lp_tok, mint, r_vault, TOKEN_PROGRAM_ID, 2_000 * POS_SCALE), &payer, &[&payer, &prop_lp_kp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_taker_tok, mint, r_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &prop_taker_kp]);

    // Refresh oracles on r_mkts[0..5] so ALL 5 markets are fresh at current slot
    let prop_slot = get_slot(&svm) + 1;
    set_slot(&mut svm, prop_slot);
    for i in 0..5 {
        send_ok(&mut svm, ix_update_oracle(prog_id, r_mkts[i], r_orc.pubkey(), 100 * POS_SCALE, 0, 0), &payer, &[&payer, &r_orc]);
    }

    // Initialize honest Multi-Market PropAMM context on `matcher_prog` (halfSpread=20bps, impact=10bps/unit, maxFill=5.0)
    // Pin immutable allowlist to ONLY the 5 whitelisted markets `r_mkts[0..5]`!
    let prop_mids: Vec<u64> = r_mkts[0..5].iter().map(|m| read_u64(&svm, m, 8)).collect();
    let prop_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
    send_ok(&mut svm, ix_init_prop_amm(matcher_prog, prop_ctx, prop_lp_kp.pubkey(), 0, 20, 10, 5 * POS_SCALE, &prop_mids), &payer, &[&payer, &prop_lp_kp]);

    // 14.1 Unbound LP MUST reject TradeWithMatcher (Custom(131))!
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx, None, 0, true, 4 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp], 131, "Unbound lpPfl rejected",
    );

    // 14.2 Unauthorized non-owner cannot bind matcherCtx!
    send_err_custom(
        &mut svm,
        ix_set_portfolio_matcher(prog_id, prop_lp_pfl, attacker.pubkey(), Some(prop_ctx)),
        &payer, &[&payer, &attacker], 111, "Non-owner SetPortfolioMatcher rejected",
    );

    // LP binds honest PropAMM while retaining 100% EOA custody of `prop_lp_pfl`!
    send_ok(&mut svm, ix_set_portfolio_matcher(prog_id, prop_lp_pfl, prop_lp_kp.pubkey(), Some(prop_ctx)), &payer, &[&payer, &prop_lp_kp]);

    // Mismatched matcherCtx, self-CPI, & aliased duplicate markets in batch rejected!
    let wrong_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, wrong_ctx, None, 0, true, 4 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp], 131, "Mismatched matcherCtx rejected",
    );
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, prog_id, prop_ctx, None, 0, true, 4 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp], 131, "Self-CPI matcherProg == percProg rejected",
    );
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher_batch(
            prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx,
            &[(r_mkts[0], 0, true, POS_SCALE, 101 * POS_SCALE), (r_mkts[0], 0, false, POS_SCALE, 99 * POS_SCALE)], None,
        ),
        &payer, &[&payer, &prop_taker_kp], 109, "Aliased duplicate market in batch rejected",
    );

    // Duplicate core/signer account passed as `extraAcc` MUST be rejected (`Custom(109)`, blocks ABI dup-stub overread!)
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx, Some(prop_taker_kp.pubkey()), 0, true, 2 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp], 109, "Aliased takerOwner passed as extraAcc rejected",
    );

    // 14.3 Single-market (k=1) CPI-Out Open Long (maxQty=8 > maxFill=5 -> partial-fill 5.0 at standalone ask = $100.70!)
    //      Also passes an optional readonly extra account to verify forwarding!
    let dummy_oracle_acc = create_prog_acc(&mut svm, &matcher_prog, 64);
    let lp_cap_0 = pfl_total_capital(&svm, &prop_lp_pfl);
    let taker_cap_0 = pfl_total_capital(&svm, &prop_taker_pfl);
    let cu_pm_open = send_ok(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx, Some(dummy_oracle_acc), 0, true, 8 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp],
    );
    assert_eq!(read_u64(&svm, &prop_ctx, 8), 1, "PropAMM seq advanced 0 -> 1");
    assert_eq!(read_u64(&svm, &prop_ctx, 16), 100_700_000, "Standalone k=1 ask price exact ($100.70 = 20+50 bps)");
    assert_eq!(read_u64(&svm, &prop_ctx, 24), 5 * POS_SCALE, "PropAMM partial fillQty capped at maxFillQty (5.0)");
    assert_eq!(pfl_total_capital(&svm, &prop_lp_pfl), lp_cap_0 + 3_500_000 - 5_000_000, "LP earned exact $3.50 spread - $5 fee");
    assert_eq!(pfl_total_capital(&svm, &prop_taker_pfl), taker_cap_0 - 3_500_000 - 5_000_000, "Taker paid exact $3.50 spread + $5 fee");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl, prop_lp_pfl, prop_taker_pfl], "suite14-k1-open");

    // 14.4 Single-market (k=1) CPI-Out Reduce Close (taker sells existing Long at standard Bid = $99.30!)
    let lp_cap_pre_c1 = pfl_total_capital(&svm, &prop_lp_pfl);
    let taker_cap_pre_c1 = pfl_total_capital(&svm, &prop_taker_pfl);
    let cu_pm_close = send_ok(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx, None, 1, true, 5 * POS_SCALE, 99 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp],
    );
    assert_eq!(read_u64(&svm, &prop_ctx, 8), 2, "PropAMM seq advanced 1 -> 2");
    assert_eq!(read_u64(&svm, &prop_ctx, 16), 99_300_000, "Standalone k=1 reduce Bid exact ($99.30 = 20+50 bps below mark)");
    assert_eq!(pfl_total_capital(&svm, &prop_lp_pfl), lp_cap_pre_c1 + 3_500_000, "LP earned ANOTHER exact $3.50 spread on reduce close!");
    assert_eq!(pfl_total_capital(&svm, &prop_taker_pfl), taker_cap_pre_c1 - 3_500_000, "Taker paid exact $3.50 spread on reduce close!");
    assert_eq!(read_u8(&svm, &prop_taker_pfl, 4), 0, "Taker closed completely via CPI-Out PropAMM!");
    assert_eq!(read_u8(&svm, &prop_lp_pfl, 4), 0, "LP closed completely via CPI-Out PropAMM!");

    // 14.5 MULTI-MARKET (k=2) ATOMIC CORRELATED BASKET IN ONE SINGLE IX & ONE CPI (ZERO TX INTROSPECTION!):
    //   Taker submits Long Mkt0 (4.0) + Short Mkt1 (4.0) in ONE TradeWithMatcher ix!
    //   PropAMM sees BOTH offers simultaneously -> grants 50% hedged-basket halfSpread discount:
    //     Standalone 4.0 spread = 20 + 40 = 60 bps ($100.60 / $99.40)
    //     Hedged k=2 basket spread = 10 + 40 = 50 bps ($100.50 on Mkt0, $99.50 on Mkt1) — strict MM price efficiency!
    //   First prove atomicity: if leg 1 violates limitPrice ($99.80 > $99.50), ENTIRE 2-leg batch reverts (0 legs opened)!
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher_batch(
            prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx,
            &[(r_mkts[0], 0, true, 4 * POS_SCALE, 101 * POS_SCALE), (r_mkts[1], 0, false, 4 * POS_SCALE, 99_800_000)], None,
        ),
        &payer, &[&payer, &prop_taker_kp], 130, "Atomic k=2 batch reverts ALL legs if leg 1 fails limitPrice",
    );
    assert_eq!(read_u8(&svm, &prop_taker_pfl, 4), 0, "Reverted k=2 batch opened ZERO legs!");

    let cu_pm_batch2 = send_ok(
        &mut svm,
        ix_trade_with_matcher_batch(
            prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx,
            &[(r_mkts[0], 0, true, 4 * POS_SCALE, 101 * POS_SCALE), (r_mkts[1], 0, false, 4 * POS_SCALE, 99 * POS_SCALE)], None,
        ),
        &payer, &[&payer, &prop_taker_kp],
    );
    assert_eq!(read_u64(&svm, &prop_ctx, 8), 3, "Multi-market k=2 batch advanced seq 2 -> 3 in ONE CPI!");
    assert_eq!(read_u64(&svm, &prop_ctx, 16), 100_500_000, "Mkt0 got hedged 50bps ask ($100.50 vs $100.60 standalone)!");
    assert_eq!(read_u64(&svm, &prop_ctx, 32), 99_500_000, "Mkt1 got hedged 50bps bid ($99.50 vs $99.40 standalone)!");
    assert_eq!(read_u8(&svm, &prop_taker_pfl, 4), 2, "Taker opened BOTH cross-margin legs in ONE TradeWithMatcher ix!");
    assert_eq!(read_u8(&svm, &prop_lp_pfl, 4), 2, "LP opened BOTH offsetting legs in ONE TradeWithMatcher ix!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl, prop_lp_pfl, prop_taker_pfl], "suite14-k2-batch-open");

    // Close BOTH legs atomically in ONE k=2 reduce batch (sell Long at Bid $99.50 + buy Short at Ask $100.50)!
    let lp_cap_pre_k2c = pfl_total_capital(&svm, &prop_lp_pfl);
    send_ok(
        &mut svm,
        ix_trade_with_matcher_batch(
            prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx,
            &[(r_mkts[0], 1, true, 4 * POS_SCALE, 99 * POS_SCALE), (r_mkts[1], 1, false, 4 * POS_SCALE, 101 * POS_SCALE)], None,
        ),
        &payer, &[&payer, &prop_taker_kp],
    );
    assert_eq!(read_u64(&svm, &prop_ctx, 16), 99_500_000, "Mkt0 reduce got hedged 50bps bid ($99.50)!");
    assert_eq!(read_u64(&svm, &prop_ctx, 32), 100_500_000, "Mkt1 reduce got hedged 50bps ask ($100.50)!");
    assert_eq!(pfl_total_capital(&svm, &prop_lp_pfl), lp_cap_pre_k2c + 4 * POS_SCALE, "LP earned exact $4.00 spread on k=2 reduce batch!");
    assert_eq!(read_u8(&svm, &prop_taker_pfl, 4), 0, "Taker closed BOTH legs in ONE k=2 reduce ix!");
    assert_eq!(read_u8(&svm, &prop_lp_pfl, 4), 0, "LP closed BOTH legs in ONE k=2 reduce ix!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl, prop_lp_pfl, prop_taker_pfl], "suite14-k2-batch-close");

    // 14.5b 5-MARKET MIXED LONG/SHORT ATOMIC BASKET IN ONE SINGLE IX & ONE 0-SIGNER CPI!
    //   Long m0 (2.0), Short m1 (2.0), Long m2 (2.0), Short m3 (2.0), Long m4 (2.0) — ALL 5 priced atomically!
    //   Hedged 5-market spread = 10 + 20 = 30 bps ($100.30 asks, $99.70 bids) vs 40 bps standalone!
    let offers_5_open = [
        (r_mkts[0], 0u8, true,  2 * POS_SCALE, 101 * POS_SCALE),
        (r_mkts[1], 0u8, false, 2 * POS_SCALE,  99 * POS_SCALE),
        (r_mkts[2], 0u8, true,  2 * POS_SCALE, 101 * POS_SCALE),
        (r_mkts[3], 0u8, false, 2 * POS_SCALE,  99 * POS_SCALE),
        (r_mkts[4], 0u8, true,  2 * POS_SCALE, 101 * POS_SCALE),
    ];
    let ix_5_open = ix_trade_with_matcher_batch(
        prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx,
        &offers_5_open, None,
    );
    let cu_pm_batch5 = send_ok(&mut svm, ix_5_open, &payer, &[&payer, &prop_taker_kp]);
    assert_eq!(read_u64(&svm, &prop_ctx, 8), 5, "5-market basket advanced seq 4 -> 5 in ONE CPI!");
    for j in 0..5 {
        let exp_p = if j % 2 == 0 { 100_300_000 } else { 99_700_000 };
        assert_eq!(read_u64(&svm, &prop_ctx, 16 + j * 16), exp_p, "5-market leg {} hedged price mismatch!", j);
        assert_eq!(read_u64(&svm, &prop_ctx, 24 + j * 16), 2 * POS_SCALE, "5-market leg {} fillQty mismatch!", j);
    }
    assert_eq!(read_u8(&svm, &prop_taker_pfl, 4), 5, "Taker opened ALL 5 mixed long/short legs in ONE ix!");
    assert_eq!(read_u8(&svm, &prop_lp_pfl, 4), 5, "LP opened ALL 5 offsetting legs in ONE ix!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl, prop_lp_pfl, prop_taker_pfl], "suite14-k5-batch-open");

    // Close ALL 5 legs atomically in ONE k=5 reduce ix (selling Longs at Bid $99.70, buying Shorts at Ask $100.30)!
    let lp_cap_pre_k5c = pfl_total_capital(&svm, &prop_lp_pfl);
    let offers_5_close = [
        (r_mkts[0], 1u8, true,  2 * POS_SCALE,  99 * POS_SCALE),
        (r_mkts[1], 1u8, false, 2 * POS_SCALE, 101 * POS_SCALE),
        (r_mkts[2], 1u8, true,  2 * POS_SCALE,  99 * POS_SCALE),
        (r_mkts[3], 1u8, false, 2 * POS_SCALE, 101 * POS_SCALE),
        (r_mkts[4], 1u8, true,  2 * POS_SCALE,  99 * POS_SCALE),
    ];
    let cu_pm_batch5_close = send_ok(
        &mut svm,
        ix_trade_with_matcher_batch(
            prog_id, r_dex, prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx,
            &offers_5_close, None,
        ),
        &payer, &[&payer, &prop_taker_kp],
    );
    for j in 0..5 {
        let exp_p = if j % 2 == 0 { 99_700_000 } else { 100_300_000 };
        assert_eq!(read_u64(&svm, &prop_ctx, 16 + j * 16), exp_p, "5-market close leg {} hedged price mismatch!", j);
    }
    assert_eq!(pfl_total_capital(&svm, &prop_lp_pfl), lp_cap_pre_k5c + 3 * POS_SCALE, "LP earned exact $3.00 spread on k=5 reduce batch!");
    assert_eq!(read_u8(&svm, &prop_taker_pfl, 4), 0, "Taker closed ALL 5 legs in ONE k=5 reduce ix!");
    assert_eq!(read_u8(&svm, &prop_lp_pfl, 4), 0, "LP closed ALL 5 legs in ONE k=5 reduce ix!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl, prop_lp_pfl, prop_taker_pfl], "suite14-k5-batch-close");

    // 14.6 Adversarial Malicious PropAMM (`evil_matcher.so`) — ALL 8 exploit modes REJECTED by core!
    let evil_ctx = create_prog_acc(&mut svm, &evil_prog, 64);
    send_ok(&mut svm, ix_set_portfolio_matcher(prog_id, prop_lp_pfl, prop_lp_kp.pubkey(), Some(evil_ctx)), &payer, &[&payer, &prop_lp_kp]);
    let evil_cases: [(u8, u64, Option<u32>, &str); 8] = [
        (0, 101 * POS_SCALE, Some(131), "Evil PropAMM over-fill (fillQty > maxQty)"),
        (1, 101 * POS_SCALE, Some(130), "Evil PropAMM abusive price violating taker limitPrice"),
        (2, 101 * POS_SCALE, Some(131), "Evil PropAMM nonzero status"),
        (3, 101 * POS_SCALE, Some(131), "Evil PropAMM stale seq / noop replay"),
        (4, 101 * POS_SCALE, Some(131), "Evil PropAMM corrupt magic"),
        (5, 101 * POS_SCALE, Some(131), "Evil PropAMM zero fill"),
        (6, 0,               Some(130), "Evil PropAMM exceeds core maxMoveBps clamp (limitPrice=0)"),
        (7, 101 * POS_SCALE, None,      "Evil PropAMM mutates readonly extraAcc"),
    ];
    for (atk_mode, lim_p, exp_code, desc) in evil_cases {
        let mut acc = svm.get_account(&evil_ctx).unwrap();
        acc.data[48] = atk_mode;
        svm.set_account(evil_ctx, acc).unwrap();
        let ix = ix_trade_with_matcher(
            prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl,
            evil_prog, evil_ctx, Some(dummy_oracle_acc), 0, true, 2 * POS_SCALE, lim_p,
        );
        if let Some(code) = exp_code {
            send_err_custom(&mut svm, ix, &payer, &[&payer, &prop_taker_kp], code, desc);
        } else {
            send_err(&mut svm, ix, &payer, &[&payer, &prop_taker_kp], desc);
        }
    }

    // Also test a pure `noop.so` matcher (owned account with pre-seeded MRET header): seq stays 0 != 1 -> Custom(131)!
    let noop_ctx = create_prog_acc(&mut svm, &fake_tok_prog, 64);
    {
        let mut acc = svm.get_account(&noop_ctx).unwrap();
        acc.data[0..4].copy_from_slice(&0x5445524Du32.to_le_bytes()); // "MRET"
        acc.data[4..8].copy_from_slice(&0u32.to_le_bytes());
        acc.data[8..16].copy_from_slice(&0u64.to_le_bytes()); // seq = 0 (stale!)
        acc.data[16..24].copy_from_slice(&(100 * POS_SCALE).to_le_bytes());
        acc.data[24..32].copy_from_slice(&(2 * POS_SCALE).to_le_bytes());
        svm.set_account(noop_ctx, acc).unwrap();
    }
    send_ok(&mut svm, ix_set_portfolio_matcher(prog_id, prop_lp_pfl, prop_lp_kp.pubkey(), Some(noop_ctx)), &payer, &[&payer, &prop_lp_kp]);
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, fake_tok_prog, noop_ctx, None, 0, true, 2 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp], 131, "noop.so stale-buffer replay rejected via seq",
    );

    // 14.7 LP revokes matcher (`None`) & withdraws 100% of EOA collateral directly (evil PropAMM CANNOT trap LP!)
    send_ok(&mut svm, ix_set_portfolio_matcher(prog_id, prop_lp_pfl, prop_lp_kp.pubkey(), None), &payer, &[&payer, &prop_lp_kp]);
    send_err_custom(
        &mut svm,
        ix_trade_with_matcher(prog_id, r_dex, r_mkts[0], prop_taker_pfl, prop_taker_kp.pubkey(), prop_lp_pfl, matcher_prog, prop_ctx, None, 0, true, 2 * POS_SCALE, 101 * POS_SCALE),
        &payer, &[&payer, &prop_taker_kp], 131, "Revoked lpPfl rejects TradeWithMatcher",
    );
    let lp_final_cap = read_u64(&svm, &prop_lp_pfl, 88);
    send_ok(&mut svm, ix_withdraw_collateral(prog_id, r_dex, prop_lp_pfl, prop_lp_kp.pubkey(), prop_lp_tok, mint, r_vault, TOKEN_PROGRAM_ID, lp_final_cap), &payer, &[&payer, &prop_lp_kp]);
    assert_eq!(read_u64(&svm, &prop_lp_pfl, 88), 0, "LP withdrew 100% EOA collateral directly!");
    assert_dex_invariants(&svm, &r_dex, &r_vault, &r_mkts, &[r_trader_pfl, r_mm_pfl, prop_lp_pfl, prop_taker_pfl], "suite14-final");
    println!("[PASS] Suite 14: Unified Single/Multi-Market CPI-Out PropAMM (0 Signer Deleg., 1-CPI k=2 & k=5 Mixed Long/Short Hedged Discount, 12 Attacks Blocked, k=1={}/{} CU, k=2={} CU, k=5 open/close={}/{} CU)", cu_pm_open, cu_pm_close, cu_pm_batch2, cu_pm_batch5, cu_pm_batch5_close);

    // =========================================================================
    // SUITE 15: ATOMIC SINGLE-TRADE POSITION FLIP (mode=4) & PERMISSIONLESS HLP VAULT!
    //   15A. Direct `Trade(mode=4)`: Long 2 -> Short 3 atomic flip in 1 ix, cross-LP close
    //        against a FLAT counterparty (auto mode=3 hand-off!), Short 2 -> Long 3 flip vs flat LP!
    //   15B. Multi-market `TradeWithMatcher` (`k=3, mode=4`): atomic 3-market basket flip
    //        (Long/Short/Long -> Short/Long/Short in ONE ix & ONE 0-signer CPI with 50% hedged discount)!
    //   15C. External Permissionless `hlp_vault.so` (ZERO core changes!):
    //        - PR #4 shareless donation capture blocked (dead-share lock!)
    //        - Lockup & stale-NAV front-running blocked (`Custom(501)`, `Custom(122)`)
    //        - Strategist binds PropAMM (`SetHlpMatcher`), earns spreads via `TradeWithMatcher(mode=4)`
    //        - Strategist executes Zero-ADL `HlpTakeoverLiquidate` (100% keeper fee auto-compounded into HLP!)
    //        - Even when strategist pauses deposits (`paused=1`), LPs withdraw 100% principal + spreads + liq fees
    //          AND auto-close `HlpReceipt` with 100% rent lamport refund!
    // =========================================================================
    let hlp_path = std::env::args()
        .nth(6)
        .unwrap_or_else(|| "build/hlp_vault.so".to_string());
    let hlp_elf = std::fs::read(&hlp_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", hlp_path, e));
    let hlp_prog = Keypair::new().pubkey();
    svm.add_program(hlp_prog, &hlp_elf).expect("hlp_vault ELF load failed");

    // Isolated fresh DEX for Suite 15 so all invariant checks are self-contained
    let h_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (h_vault, h_vbump) = derive_dex_vault(&prog_id, &h_dex);
    let h_orc = Keypair::new();
    let h_strat = Keypair::new();
    let h_lp1 = Keypair::new();
    let h_lp2 = Keypair::new();
    let h_taker = Keypair::new();
    let h_flat_lp = Keypair::new();
    let h_victim = Keypair::new();
    for kp in [&h_orc, &h_strat, &h_lp1, &h_lp2, &h_taker, &h_flat_lp, &h_victim] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    send_ok(&mut svm, ix_init_dex(prog_id, h_dex, dex_admin.pubkey(), mint, h_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, h_vbump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);

    let mut h_mkts: Vec<Address> = Vec::new();
    for _ in 0..3 {
        let m = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        send_ok(&mut svm, ix_create_market(
            prog_id, h_dex, m, mint, h_orc.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault,
            100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE,
        ), &payer, &[&payer, &dex_admin]);
        h_mkts.push(m);
    }

    let h_taker_tok = create_tok_acc(&mut svm, &mint, &h_taker.pubkey(), 5_000 * POS_SCALE);
    let h_flat_tok  = create_tok_acc(&mut svm, &mint, &h_flat_lp.pubkey(), 5_000 * POS_SCALE);
    let h_lp1_tok   = create_tok_acc(&mut svm, &mint, &h_lp1.pubkey(), 5_000 * POS_SCALE);
    let h_lp2_tok   = create_tok_acc(&mut svm, &mint, &h_lp2.pubkey(), 5_000 * POS_SCALE);
    let h_vic_tok   = create_tok_acc(&mut svm, &mint, &h_victim.pubkey(), 5_000 * POS_SCALE);
    let h_atk_tok   = create_tok_acc(&mut svm, &mint, &attacker.pubkey(), 5_000 * POS_SCALE);

    let h_taker_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let h_flat_pfl  = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let h_vic_pfl   = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    for (pfl, kp, tok, dep) in [
        (h_taker_pfl, &h_taker, h_taker_tok, 1_000 * POS_SCALE),
        (h_flat_pfl,  &h_flat_lp, h_flat_tok, 1_000 * POS_SCALE),
        (h_vic_pfl,   &h_victim, h_vic_tok, 105 * POS_SCALE),
    ] {
        send_ok(&mut svm, ix_init_portfolio(prog_id, h_dex, pfl, kp.pubkey()), &payer, &[&payer, kp]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, h_dex, pfl, kp.pubkey(), tok, mint, h_vault, TOKEN_PROGRAM_ID, dep), &payer, &[&payer, kp]);
    }

    // 15A. Direct Trade(mode=4): Atomic Long 2 -> Short 3 flip, plus cross-LP close & flip vs FLAT LP!
    let h_cp1 = Keypair::new();
    svm.airdrop(&h_cp1.pubkey(), 1_000_000_000).unwrap();
    let h_cp1_tok = create_tok_acc(&mut svm, &mint, &h_cp1.pubkey(), 2_000 * POS_SCALE);
    let h_cp1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, h_dex, h_cp1_pfl, h_cp1.pubkey()), &payer, &[&payer, &h_cp1]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, h_dex, h_cp1_pfl, h_cp1.pubkey(), h_cp1_tok, mint, h_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &h_cp1]);

    // Open Long 2.0 on h_taker vs Short 2.0 on h_cp1 via mode=4!
    send_ok(&mut svm, ix_trade(prog_id, h_dex, h_mkts[0], h_taker_pfl, h_taker.pubkey(), h_cp1_pfl, h_cp1.pubkey(), 4, 2 * POS_SCALE), &payer, &[&payer, &h_taker, &h_cp1]);
    assert_eq!(read_u8(&svm, &h_taker_pfl, LEG_HEADER + 1), 1, "Taker opened Long via mode=4");
    assert_eq!(read_u64(&svm, &h_taker_pfl, LEG_HEADER + 48), 2 * POS_SCALE);

    // Atomic Flip: h_cp1 buys 5.0 from h_taker in ONE instruction (closes 2.0 + flips h_taker to Short 3.0, h_cp1 to Long 3.0)!
    let cu_direct_flip = send_ok(&mut svm, ix_trade(prog_id, h_dex, h_mkts[0], h_cp1_pfl, h_cp1.pubkey(), h_taker_pfl, h_taker.pubkey(), 4, 5 * POS_SCALE), &payer, &[&payer, &h_cp1, &h_taker]);
    assert_eq!(read_u8(&svm, &h_taker_pfl, LEG_HEADER + 1), 2, "Taker atomically flipped Long 2 -> Short 3!");
    assert_eq!(read_u64(&svm, &h_taker_pfl, LEG_HEADER + 48), 3 * POS_SCALE);
    assert_eq!(read_u8(&svm, &h_cp1_pfl, LEG_HEADER + 1), 1, "CP1 atomically flipped Short 2 -> Long 3!");
    assert_eq!(read_u64(&svm, &h_cp1_pfl, LEG_HEADER + 48), 3 * POS_SCALE);

    // Cross-LP Atomic Flip vs brand-new FLAT LP (`h_flat_pfl` has 0 position!):
    //   h_taker buys 5.0 from FLAT h_flat_pfl -> auto mode=3 hands off Short 3.0 to h_flat_pfl + mode=0 opens Long 2.0 on h_taker (Short 5.0 on h_flat_pfl)!
    send_ok(&mut svm, ix_trade(prog_id, h_dex, h_mkts[0], h_taker_pfl, h_taker.pubkey(), h_flat_pfl, h_flat_lp.pubkey(), 4, 5 * POS_SCALE), &payer, &[&payer, &h_taker, &h_flat_lp]);
    assert_eq!(read_u8(&svm, &h_taker_pfl, LEG_HEADER + 1), 1, "Taker flipped Short 3 -> Long 2 against FLAT LP!");
    assert_eq!(read_u64(&svm, &h_taker_pfl, LEG_HEADER + 48), 2 * POS_SCALE);
    assert_eq!(read_u8(&svm, &h_flat_pfl, LEG_HEADER + 1), 2, "Flat LP absorbed Short 3 + opened Short 2 = Short 5!");
    assert_eq!(read_u64(&svm, &h_flat_pfl, LEG_HEADER + 48), 5 * POS_SCALE);
    assert_eq!(read_u64(&svm, &h_mkts[0], 256), 5 * POS_SCALE, "OI grew cleanly from 3 -> 5 (hand-off 3 OI-invariant + open 2)!");
    // Cleanly close h_taker & h_cp1 & h_flat_pfl back to 0 on mkt0
    send_ok(&mut svm, ix_trade(prog_id, h_dex, h_mkts[0], h_flat_pfl, h_flat_lp.pubkey(), h_taker_pfl, h_taker.pubkey(), 4, 2 * POS_SCALE), &payer, &[&payer, &h_flat_lp, &h_taker]);
    send_ok(&mut svm, ix_trade(prog_id, h_dex, h_mkts[0], h_flat_pfl, h_flat_lp.pubkey(), h_cp1_pfl, h_cp1.pubkey(), 4, 3 * POS_SCALE), &payer, &[&payer, &h_flat_lp, &h_cp1]);
    assert_eq!(read_u64(&svm, &h_mkts[0], 256), 0, "Mkt0 returned cleanly to 0 OI!");

    // 15C. External Permissionless HLP Vault (`hlp_vault.so`) + Multi-Market PropAMM Flip (`mode=4`)!
    let h_mids: Vec<u64> = h_mkts.iter().map(|m| read_u64(&svm, m, 8)).collect();
    let hlp_vault = create_prog_acc(&mut svm, &hlp_prog, HLP_SIZE);
    let (hlp_pda, hlp_bump) = Address::find_program_address(&[b"hlpv", hlp_vault.as_ref()], &hlp_prog);
    let hlp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let hlp_fee_tok = create_tok_acc(&mut svm, &mint, &hlp_pda, 0);
    let hlp_prop_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
    send_ok(&mut svm, ix_init_prop_amm(matcher_prog, hlp_prop_ctx, h_strat.pubkey(), 0, 20, 10, 10 * POS_SCALE, &h_mids), &payer, &[&payer, &h_strat]);

    // Fake non-SPL `hlpFeeTok` rejected (`Custom(505)`)!
    let fake_fee_tok = create_prog_acc(&mut svm, &hlp_prog, 165);
    {
        let mut a = svm.get_account(&fake_fee_tok).unwrap();
        a.data[0..32].copy_from_slice(mint.as_ref());
        a.data[32..64].copy_from_slice(hlp_pda.as_ref());
        a.data[108] = 1;
        svm.set_account(fake_fee_tok, a).unwrap();
    }
    send_err_custom(&mut svm, ix_init_hlp_vault(
        hlp_prog, hlp_vault, h_strat.pubkey(), h_dex, hlp_pfl, hlp_pda, fake_fee_tok, prog_id,
        matcher_prog, hlp_bump, 10, 0, POS_SCALE, &h_mids,
    ), &payer, &[&payer, &h_strat], 505, "InitHlpVault rejects fake non-SPL hlpFeeTok");

    let cu_hlp_init = send_ok(&mut svm, ix_init_hlp_vault(
        hlp_prog, hlp_vault, h_strat.pubkey(), h_dex, hlp_pfl, hlp_pda, hlp_fee_tok, prog_id,
        matcher_prog, hlp_bump, 10, 0, POS_SCALE, &h_mids,
    ), &payer, &[&payer, &h_strat]);

    // Attack 1 (PR #4 Shareless Donation Capture): attacker donates $10 directly to hlp_pfl while totalShares == 0,
    // then deposits $5 via DepositHlp -> $10 is locked behind 10M dead shares, attacker ONLY gets $5 back!
    send_ok(&mut svm, ix_deposit_collateral(prog_id, h_dex, hlp_pfl, attacker.pubkey(), h_atk_tok, mint, h_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE), &payer, &[&payer, &attacker]);
    let atk_rec = create_prog_acc(&mut svm, &hlp_prog, HLP_REC_SIZE);
    let atk_tok_pre = token_amount(&svm, &h_atk_tok);
    send_ok(&mut svm, ix_deposit_hlp(hlp_prog, hlp_vault, atk_rec, attacker.pubkey(), h_atk_tok, h_dex, hlp_pfl, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, 5 * POS_SCALE), &payer, &[&payer, &attacker]);
    assert_eq!(read_u64(&svm, &hlp_vault, 184), 15 * POS_SCALE, "HLP locked 10M direct donation behind dead shares + 5M attacker shares!");
    assert_eq!(read_u64(&svm, &atk_rec, 72), 5 * POS_SCALE);

    // Attack 2 (Lockup enforcement): withdraw before +10 slots REJECTED (Custom(501))!
    send_err_custom(&mut svm, ix_withdraw_hlp(
        hlp_prog, hlp_vault, atk_rec, attacker.pubkey(), h_atk_tok, h_dex, hlp_pfl, hlp_pda, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, 5 * POS_SCALE,
    ), &payer, &[&payer, &attacker], 501, "HLP lockup blocks early withdraw");
    let sl_unlock = get_slot(&svm) + 10;
    set_slot(&mut svm, sl_unlock);
    let atk_lam_pre = svm.get_account(&attacker.pubkey()).unwrap().lamports;
    let atk_rec_lam = svm.get_account(&atk_rec).unwrap().lamports;
    send_ok(&mut svm, ix_withdraw_hlp(
        hlp_prog, hlp_vault, atk_rec, attacker.pubkey(), h_atk_tok, h_dex, hlp_pfl, hlp_pda, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, 5 * POS_SCALE,
    ), &payer, &[&payer, &attacker]);
    assert_eq!(token_amount(&svm, &h_atk_tok), atk_tok_pre, "PR #4 blocked: attacker recovered ONLY $5 (0 stolen donation!)");
    assert_eq!(svm.get_account(&attacker.pubkey()).unwrap().lamports, atk_lam_pre + atk_rec_lam, "WithdrawHlp auto-closed empty HlpReceipt & refunded 100% rent!");

    // LP1 ($500) & LP2 ($500) deposit into HLP Vault!
    let lp1_rec = create_prog_acc(&mut svm, &hlp_prog, HLP_REC_SIZE);
    let lp2_rec = create_prog_acc(&mut svm, &hlp_prog, HLP_REC_SIZE);
    let cu_hlp_dep = send_ok(&mut svm, ix_deposit_hlp(hlp_prog, hlp_vault, lp1_rec, h_lp1.pubkey(), h_lp1_tok, h_dex, hlp_pfl, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, 500 * POS_SCALE), &payer, &[&payer, &h_lp1]);
    send_ok(&mut svm, ix_deposit_hlp(hlp_prog, hlp_vault, lp2_rec, h_lp2.pubkey(), h_lp2_tok, h_dex, hlp_pfl, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, 500 * POS_SCALE), &payer, &[&payer, &h_lp2]);
    assert_eq!(read_u64(&svm, &hlp_pfl, 88), 1_010 * POS_SCALE, "HLP Portfolio funded with $1,010!");

    // Strategist binds PropAMM (`SetHlpMatcher`, Op 1); unauthorized attacker rejected (Custom(102))!
    send_err_custom(&mut svm, ix_set_hlp_matcher(hlp_prog, hlp_vault, attacker.pubkey(), hlp_pfl, hlp_pda, prog_id, Some(hlp_prop_ctx), None), &payer, &[&payer, &attacker], 102, "Non-strategist SetHlpMatcher rejected");
    send_ok(&mut svm, ix_set_hlp_matcher(hlp_prog, hlp_vault, h_strat.pubkey(), hlp_pfl, hlp_pda, prog_id, Some(hlp_prop_ctx), None), &payer, &[&payer, &h_strat]);

    // 15B. Multi-Market (`k=3`) PropAMM Atomic Basket Flip against HLP Vault (`mode=4`)!
    //   1) Taker opens [Long m0 (2), Short m1 (2), Long m2 (2)] vs HLP Vault in ONE ix!
    let hlp_cap_pre_mm = read_u64(&svm, &hlp_pfl, 88);
    send_ok(&mut svm, ix_trade_with_matcher_batch(
        prog_id, h_dex, h_taker_pfl, h_taker.pubkey(), hlp_pfl, matcher_prog, hlp_prop_ctx,
        &[(h_mkts[0], 4, true, 2 * POS_SCALE, 101 * POS_SCALE), (h_mkts[1], 4, false, 2 * POS_SCALE, 99 * POS_SCALE), (h_mkts[2], 4, true, 2 * POS_SCALE, 101 * POS_SCALE)], None,
    ), &payer, &[&payer, &h_taker]);
    assert_eq!(read_u8(&svm, &h_taker_pfl, 4), 3, "Taker opened 3 legs vs HLP via mode=4!");

    //   2) Attack 3 (Stale-NAV front-running): advance 1 slot -> DepositHlp & WithdrawHlp MUST reject (Custom(122))!
    let sl_stale = get_slot(&svm) + 1;
    set_slot(&mut svm, sl_stale);
    send_err_custom(&mut svm, ix_deposit_hlp(hlp_prog, hlp_vault, lp1_rec, h_lp1.pubkey(), h_lp1_tok, h_dex, hlp_pfl, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, POS_SCALE), &payer, &[&payer, &h_lp1], 122, "HLP blocks DepositHlp with stale open leg");

    //   3) Atomic 3-Market Flip in ONE tx after slot advance (atomic [RefreshLeg(m1,m2) + TradeWithMatcher(k=3, mode=4)]!)
    //      Taker flips ALL 3 positions simultaneously: [Long 2 -> Short 2, Short 2 -> Long 2, Long 2 -> Short 2] (qty=4 each, hedged 50% discount)!
    let cu_batch3_flip = send_ixs_ok(&mut svm, &[
        ix_refresh_leg(prog_id, h_dex, h_mkts[1], h_taker_pfl, false),
        ix_refresh_leg(prog_id, h_dex, h_mkts[2], h_taker_pfl, false),
        ix_refresh_leg(prog_id, h_dex, h_mkts[1], hlp_pfl, false),
        ix_refresh_leg(prog_id, h_dex, h_mkts[2], hlp_pfl, false),
        ix_trade_with_matcher_batch(
            prog_id, h_dex, h_taker_pfl, h_taker.pubkey(), hlp_pfl, matcher_prog, hlp_prop_ctx,
            &[(h_mkts[0], 4, false, 4 * POS_SCALE, 99 * POS_SCALE), (h_mkts[1], 4, true, 4 * POS_SCALE, 101 * POS_SCALE), (h_mkts[2], 4, false, 4 * POS_SCALE, 99 * POS_SCALE)], None,
        ),
    ], &payer, &[&payer, &h_taker]);
    assert_eq!(read_u8(&svm, &h_taker_pfl, 4), 3, "Taker still holds all 3 flipped legs!");
    // Close all 3 taker legs vs HLP Vault cleanly (mode=4) so HLP realized spreads!
    send_ok(&mut svm, ix_trade_with_matcher_batch(
        prog_id, h_dex, h_taker_pfl, h_taker.pubkey(), hlp_pfl, matcher_prog, hlp_prop_ctx,
        &[(h_mkts[0], 4, true, 2 * POS_SCALE, 101 * POS_SCALE), (h_mkts[1], 4, false, 2 * POS_SCALE, 99 * POS_SCALE), (h_mkts[2], 4, true, 2 * POS_SCALE, 101 * POS_SCALE)], None,
    ), &payer, &[&payer, &h_taker]);
    assert_eq!(read_u8(&svm, &hlp_pfl, 4), 0, "HLP flat after taker round-trip!");
    let hlp_cap_post_mm = read_u64(&svm, &hlp_pfl, 88);
    assert!(hlp_cap_post_mm > hlp_cap_pre_mm, "HLP Vault earned real PropAMM spreads across open + atomic 3-market flip + close!");

    // 15D. Zero-ADL HLP Liquidation Takeover (`HlpTakeoverLiquidate`, Op 4) with 100% auto-compounded keeper fee!
    //   Victim opens Long 10.0 on mkt0 vs h_cp1 ($105 capital -> IM=$100, MM=$50); price drops $100 -> $94 -> underwater!
    send_ok(&mut svm, ix_trade(prog_id, h_dex, h_mkts[0], h_vic_pfl, h_victim.pubkey(), h_cp1_pfl, h_cp1.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &h_victim, &h_cp1]);
    step_oracle(&mut svm, prog_id, h_mkts[0], &h_orc, 94 * POS_SCALE, &payer);
    let hlp_cap_pre_liq = pfl_total_capital(&svm, &hlp_pfl);
    let cu_hlp_liq = send_ok(&mut svm, ix_hlp_takeover_liquidate(
        hlp_prog, hlp_vault, h_strat.pubkey(), h_dex, h_mkts[0], h_vic_pfl, hlp_fee_tok,
        mint, h_vault, TOKEN_PROGRAM_ID, hlp_pfl, hlp_pda, prog_id, 0,
    ), &payer, &[&payer, &h_strat]);
    assert_eq!(read_u64(&svm, &h_mkts[0], 288), ADL_ONE, "HLP takeover caused ZERO ADL on longs!");
    assert_eq!(read_u64(&svm, &h_mkts[0], 296), ADL_ONE, "HLP takeover caused ZERO ADL on shorts!");
    assert_eq!(token_amount(&svm, &hlp_fee_tok), 0, "100% of keeper liquidation fee swept from hlpFeeTok into hlpPfl!");
    let hlp_cap_post_liq = pfl_total_capital(&svm, &hlp_pfl);
    assert!(hlp_cap_post_liq > hlp_cap_pre_liq, "HLP Portfolio capital grew directly from auto-compounded liquidation takeover fee!");
    // Close HLP's taken-over Long 10.0 cleanly against h_cp1 at mark so LPs can withdraw 100%!
    send_ok(&mut svm, ix_trade_with_matcher(prog_id, h_dex, h_mkts[0], h_cp1_pfl, h_cp1.pubkey(), hlp_pfl, matcher_prog, hlp_prop_ctx, None, 4, true, 10 * POS_SCALE, 96 * POS_SCALE), &payer, &[&payer, &h_cp1]);
    assert_eq!(read_u8(&svm, &hlp_pfl, 4), 0, "HLP closed taken-over position cleanly!");

    // 15E. Attack 4 (Strategist cannot pause withdrawals!): strategist pauses deposits (`paused=1`) ->
    //      DepositHlp blocked (Custom(500)), YET LP1 & LP2 withdraw 100% of principal + ALL compounded yield + rent!
    send_ok(&mut svm, ix_set_hlp_matcher(hlp_prog, hlp_vault, h_strat.pubkey(), hlp_pfl, hlp_pda, prog_id, None, Some(1)), &payer, &[&payer, &h_strat]);
    let sl_done = get_slot(&svm) + 10;
    set_slot(&mut svm, sl_done);
    send_err_custom(&mut svm, ix_deposit_hlp(hlp_prog, hlp_vault, lp1_rec, h_lp1.pubkey(), h_lp1_tok, h_dex, hlp_pfl, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, POS_SCALE), &payer, &[&payer, &h_lp1], 500, "Paused HLP blocks new deposits");

    let lp1_tok_pre = token_amount(&svm, &h_lp1_tok);
    let lp2_tok_pre = token_amount(&svm, &h_lp2_tok);
    let lp1_sh = read_u64(&svm, &lp1_rec, 72);
    let lp2_sh = read_u64(&svm, &lp2_rec, 72);
    let cu_hlp_wdr = send_ok(&mut svm, ix_withdraw_hlp(hlp_prog, hlp_vault, lp1_rec, h_lp1.pubkey(), h_lp1_tok, h_dex, hlp_pfl, hlp_pda, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, lp1_sh), &payer, &[&payer, &h_lp1]);
    send_ok(&mut svm, ix_withdraw_hlp(hlp_prog, hlp_vault, lp2_rec, h_lp2.pubkey(), h_lp2_tok, h_dex, hlp_pfl, hlp_pda, mint, h_vault, TOKEN_PROGRAM_ID, prog_id, lp2_sh), &payer, &[&payer, &h_lp2]);
    let lp1_out = token_amount(&svm, &h_lp1_tok) - lp1_tok_pre;
    let lp2_out = token_amount(&svm, &h_lp2_tok) - lp2_tok_pre;
    assert!(lp1_out > 500 * POS_SCALE, "LP1 withdrew >$500 principal (earned PropAMM spreads + liq fees = {})!", lp1_out);
    assert!(lp2_out > 500 * POS_SCALE, "LP2 withdrew >$500 principal (earned PropAMM spreads + liq fees = {})!", lp2_out);
    assert_dex_invariants(&svm, &h_dex, &h_vault, &h_mkts, &[h_taker_pfl, h_flat_pfl, h_vic_pfl, h_cp1_pfl, hlp_pfl], "suite15-final");
    println!(
        "[PASS] Suite 15: Atomic Position Flip (mode=4, direct={} CU, k=3 PropAMM flip={} CU) + External HLP Vault ({} B, init={} dep={} liq={} wdr={} CU, LP1/LP2 profit=+{}/+{} uUSDC, 0 ADL, 0 rug!)",
        cu_direct_flip, cu_batch3_flip, hlp_elf.len(), cu_hlp_init, cu_hlp_dep, cu_hlp_liq, cu_hlp_wdr,
        lp1_out - 500 * POS_SCALE, lp2_out - 500 * POS_SCALE
    );

    // =========================================================================
    // SUITE 16: FULL ADVERSARIAL RED-TEAM EXPLOIT REGRESSIONS (ALL 7 GAPS PROVEN!)
    //   16A. Exact Cross-Market Contagion Exploit (`M_atk -> I_BTC`) DEFEATED:
    //        - `P_atk` deposits $200, opens Long $1,000 honest BTC (`M_real`, mm=$50)
    //          + Short $1,000 permissionless `M_atk` (mm=$50).
    //        - Attacker pumps `M_atk` +25% and refreshes/liquidates `M_atk` to drain
    //          shared `freeCapital -> 0` and `M_atk.lockedMm -> 0` (incl. `liqFee`!).
    //        - Per-leg `lockedMm` firewall keeps `BTC.lockedMm == $50` 100% INTACT!
    //        - Honest `BTC` drops -0.75% -> `Liquidate(BTC, P_atk)` pays full loss +
    //          `liqFee` strictly from `BTC.lockedMm` -> EXACT `shortfall == 0` & `I_BTC` draw == 0!
    //   16B. Anonymous Unlisted-Market Drain via `matcher.so` REJECTED (`Custom(201)`):
    //        - Attacker creates `M_scam` not in PropAMM allowlist -> `TradeWithMatcher` fails!
    //   16C. HLP Strategist Rug Vectors ALL REJECTED (`Custom(507)`, `Custom(508)`):
    //        - Binding `evil_matcher.so` ctx -> `Custom(507)`
    //        - Binding PropAMM ctx whose allowlist includes `M_scam` -> `Custom(508)`
    //        - `HlpTakeoverLiquidate` on unlisted `M_scam` -> `Custom(508)`
    //   16D. `mode = 2/3` Hand-Off Trade-Fee Bypass FIXED:
    //        - Incoming opening buyer in `mode=2` (L->L) and `mode=3` (S->S) pays exact `tradeFeeBps`!
    // =========================================================================
    {
        let x_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (x_vault, x_vbump) = derive_dex_vault(&prog_id, &x_dex);
        send_ok(&mut svm, ix_init_dex(prog_id, x_dex, dex_admin.pubkey(), mint, x_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, x_vbump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let x_sl = get_slot(&svm) + 10;
        set_slot(&mut svm, x_sl);

        let x_btc_orc = Keypair::new();
        let x_atk_orc = Keypair::new();
        let x_btc_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let x_atk_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let x_fee_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let x_btc_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);

        // Honest BTC (`M_real`): $100, im=10%, mm=5%, liqFee=1%, maxMove=0.75% (K+1=5 safe)
        send_ok(&mut svm, ix_create_market(prog_id, x_dex, x_btc_mkt, mint, x_btc_orc.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        // Permissionless attacker market (`M_atk`): $100, same params, attacker controls `x_atk_orc`
        send_ok(&mut svm, ix_create_market(prog_id, x_dex, x_atk_mkt, mint, x_atk_orc.pubkey(), attacker.pubkey(), attacker_tok, fee_vault, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &attacker]);
        // Fee-bearing market for 16D (`tradeFeeBps = 50` = 0.50%)
        send_ok(&mut svm, ix_create_market(prog_id, x_dex, x_fee_mkt, mint, x_btc_orc.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 50, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);

        // Seed honest I_BTC with $500!
        send_ok(&mut svm, ix_deposit_insurance(prog_id, x_dex, x_btc_mkt, x_btc_ins, lp.pubkey(), lp_tok, mint, x_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);

        let p_atk_kp = Keypair::new();
        let p_btc_s_kp = Keypair::new();
        let p_scam_l_kp = Keypair::new();
        for kp in [&p_atk_kp, &p_btc_s_kp, &p_scam_l_kp] {
            svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
        }
        let p_atk_tok = create_tok_acc(&mut svm, &mint, &p_atk_kp.pubkey(), 2_000 * POS_SCALE);
        let p_btc_s_tok = create_tok_acc(&mut svm, &mint, &p_btc_s_kp.pubkey(), 2_000 * POS_SCALE);
        let p_scam_l_tok = create_tok_acc(&mut svm, &mint, &p_scam_l_kp.pubkey(), 2_000 * POS_SCALE);

        let p_atk = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let p_btc_s = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let p_scam_l = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        for (p, kp, t, dep) in [
            (p_atk, &p_atk_kp, p_atk_tok, 200 * POS_SCALE),
            (p_btc_s, &p_btc_s_kp, p_btc_s_tok, 1_000 * POS_SCALE),
            (p_scam_l, &p_scam_l_kp, p_scam_l_tok, 1_000 * POS_SCALE),
        ] {
            send_ok(&mut svm, ix_init_portfolio(prog_id, x_dex, p, kp.pubkey()), &payer, &[&payer, kp]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, x_dex, p, kp.pubkey(), t, mint, x_vault, TOKEN_PROGRAM_ID, dep), &payer, &[&payer, kp]);
        }

        // 16A: Exact user contagion attack!
        //   P_atk opens Long 10 BTC ($1,000, mm=$50) + Short 10 M_atk ($1,000, mm=$50) on $200 capital!
        send_ok(&mut svm, ix_trade(prog_id, x_dex, x_btc_mkt, p_atk, p_atk_kp.pubkey(), p_btc_s, p_btc_s_kp.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &p_atk_kp, &p_btc_s_kp]);
        send_ok(&mut svm, ix_trade(prog_id, x_dex, x_atk_mkt, p_scam_l, p_scam_l_kp.pubkey(), p_atk, p_atk_kp.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &p_scam_l_kp, &p_atk_kp]);
        let x_btc_mid = read_u64(&svm, &x_btc_mkt, 8);
        let x_atk_mid = read_u64(&svm, &x_atk_mkt, 8);
        assert_eq!(leg_locked_mm_for_mkt(&svm, &p_atk, x_btc_mid), 50 * POS_SCALE);
        assert_eq!(leg_locked_mm_for_mkt(&svm, &p_atk, x_atk_mid), 50 * POS_SCALE);
        assert_eq!(pfl_free_capital(&svm, &p_atk), 100 * POS_SCALE);

        // Attacker pumps M_atk +25% ($100 -> $125, -$250 loss on P_atk) & refreshes/liquidates M_atk!
        step_oracle(&mut svm, prog_id, x_atk_mkt, &x_atk_orc, 125 * POS_SCALE, &payer);
        let sl_16a = get_slot(&svm) + 1;
        set_slot(&mut svm, sl_16a);
        send_ok(&mut svm, ix_update_oracle(prog_id, x_btc_mkt, x_btc_orc.pubkey(), 100 * POS_SCALE, 0, 0), &payer, &[&payer, &x_btc_orc]);
        // Bankrupt `RefreshLeg(M_atk, P_atk)` is rejected (`Custom(107)`, #109);
        // `Liquidate(M_atk, P_atk)` settles `M_atk` directly, draining freeCapital -> 0 & M_atk.lockedMm -> 0
        // (including any keeper liqFee attempt on M_atk!), YET BTC.lockedMm MUST remain EXACT $50!
        send_err_custom(&mut svm, ix_refresh_leg(prog_id, x_dex, x_atk_mkt, p_atk, false),
            &payer, &[&payer], 107, "16A: bankrupt RefreshLeg(M_atk) rejected (Custom 107)");
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, x_dex, x_btc_mkt, p_atk, false),
            ix_liquidate(prog_id, x_dex, x_atk_mkt, p_atk, keeper_tok, mint, x_vault, TOKEN_PROGRAM_ID),
        ], &payer, &[&payer]);
        assert_eq!(pfl_free_capital(&svm, &p_atk), 0, "16A: freeCapital drained to 0 by M_atk");
        assert_eq!(leg_locked_mm_for_mkt(&svm, &p_atk, x_atk_mid), 0, "16A: M_atk leg closed & lockedMm == 0");
        assert_eq!(leg_locked_mm_for_mkt(&svm, &p_atk, x_btc_mid), 50 * POS_SCALE, "16A FIREWALL: BTC.lockedMm == $50 BIT-FOR-BIT INTACT despite M_atk bankruptcy + liqFee!");

        // Honest BTC ticks down -0.75% ($100 -> $99.25): P_atk equity on BTC = $50 - $7.50 = $42.50 < MM ($49.625)!
        // Keeper liquidates P_atk on BTC: full -$7.50 loss + $9.925 liqFee paid strictly out of BTC.lockedMm ($50)!
        let i_btc_pre = read_u64(&svm, &x_btc_mkt, 224);
        set_slot(&mut svm, sl_16a + 1);
        send_ok(&mut svm, ix_update_oracle(prog_id, x_btc_mkt, x_btc_orc.pubkey(), 99_250_000, 0, 0), &payer, &[&payer, &x_btc_orc]);
        send_ok(&mut svm, ix_liquidate(prog_id, x_dex, x_btc_mkt, p_atk, keeper_tok, mint, x_vault, TOKEN_PROGRAM_ID), &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &x_btc_mkt, 224), i_btc_pre, "16A PROVEN: ZERO cross-market contagion! Honest I_BTC draw == 0!");
        assert_eq!(read_u64(&svm, &x_btc_mkt, 216), 7_500_000, "16A PROVEN: Honest BTC counterparty receives 100% of $7.50 profit in R_BTC!");
        assert_dex_invariants(&svm, &x_dex, &x_vault, &[x_btc_mkt, x_atk_mkt, x_fee_mkt], &[p_atk, p_btc_s, p_scam_l], "16A-post-contagion-defeated");

        // 16B & 16C: Anonymous M_scam drain via matcher.so (Custom(201)) + HLP Strategist Rugs (Custom(507/508))!
        let x_hlp_vault = create_prog_acc(&mut svm, &hlp_prog, HLP_SIZE);
        let (x_hlp_pda, x_hlp_bump) = Address::find_program_address(&[b"hlpv", x_hlp_vault.as_ref()], &hlp_prog);
        let x_hlp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let x_hlp_fee_tok = create_tok_acc(&mut svm, &mint, &x_hlp_pda, 0);
        // Pin HLP Vault ONLY to `matcher_prog` and ONLY to honest `[x_btc_mid]`!
        send_ok(&mut svm, ix_init_hlp_vault(
            hlp_prog, x_hlp_vault, h_strat.pubkey(), x_dex, x_hlp_pfl, x_hlp_pda, x_hlp_fee_tok, prog_id,
            matcher_prog, x_hlp_bump, 0, 0, POS_SCALE, &[x_btc_mid],
        ), &payer, &[&payer, &h_strat]);
        // Fund HLP with $500 from honest LP
        let x_lp_rec = create_prog_acc(&mut svm, &hlp_prog, HLP_REC_SIZE);
        let x_lp_tok = create_tok_acc(&mut svm, &mint, &h_lp1.pubkey(), 1_000 * POS_SCALE);
        send_ok(&mut svm, ix_deposit_hlp(hlp_prog, x_hlp_vault, x_lp_rec, h_lp1.pubkey(), x_lp_tok, x_dex, x_hlp_pfl, mint, x_vault, TOKEN_PROGRAM_ID, prog_id, 500 * POS_SCALE), &payer, &[&payer, &h_lp1]);

        // 16C-1: Strategist tries to bind `evil_matcher.so` ctx -> REJECTED Custom(507) (`HErr.matcherNotAllowed`)!
        let x_evil_ctx = create_prog_acc(&mut svm, &evil_prog, PROP_AMM_SIZE);
        send_err_custom(&mut svm, ix_set_hlp_matcher(hlp_prog, x_hlp_vault, h_strat.pubkey(), x_hlp_pfl, x_hlp_pda, prog_id, Some(x_evil_ctx), None), &payer, &[&payer, &h_strat], 507, "16C-1: HLP rejects evil_matcher.so ctx");

        // 16C-2: Strategist creates honest matcher.so ctx allowing `[x_btc_mid, x_atk_mid]` -> REJECTED Custom(508) (`HErr.marketNotAllowed`)!
        let x_scam_prop_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
        send_ok(&mut svm, ix_init_prop_amm(matcher_prog, x_scam_prop_ctx, h_strat.pubkey(), 0, 20, 10, 10 * POS_SCALE, &[x_btc_mid, x_atk_mid]), &payer, &[&payer, &h_strat]);
        send_err_custom(&mut svm, ix_set_hlp_matcher(hlp_prog, x_hlp_vault, h_strat.pubkey(), x_hlp_pfl, x_hlp_pda, prog_id, Some(x_scam_prop_ctx), None), &payer, &[&payer, &h_strat], 508, "16C-2: HLP rejects PropAMM ctx allowing unlisted M_atk");

        // Strategist binds valid PropAMM ctx allowing ONLY `[x_btc_mid]` -> SUCCEEDS!
        let x_good_prop_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
        send_ok(&mut svm, ix_init_prop_amm(matcher_prog, x_good_prop_ctx, h_strat.pubkey(), 0, 20, 10, 10 * POS_SCALE, &[x_btc_mid]), &payer, &[&payer, &h_strat]);
        send_ok(&mut svm, ix_set_hlp_matcher(hlp_prog, x_hlp_vault, h_strat.pubkey(), x_hlp_pfl, x_hlp_pda, prog_id, Some(x_good_prop_ctx), None), &payer, &[&payer, &h_strat]);

        // 16B: Anonymous attacker tries TradeWithMatcher on unlisted `x_atk_mkt` against HLP -> REJECTED Custom(201) (`MErr.marketNotAllowed`)!
        send_err_custom(&mut svm, ix_trade_with_matcher(prog_id, x_dex, x_atk_mkt, p_scam_l, p_scam_l_kp.pubkey(), x_hlp_pfl, matcher_prog, x_good_prop_ctx, None, 0, true, POS_SCALE, 130 * POS_SCALE), &payer, &[&payer, &p_scam_l_kp], 201, "16B: PropAMM rejects unlisted M_scam quote");

        // 16C-3: Strategist tries HlpTakeoverLiquidate on unlisted `x_atk_mkt` -> REJECTED Custom(508) (`HErr.marketNotAllowed`)!
        send_err_custom(&mut svm, ix_hlp_takeover_liquidate(hlp_prog, x_hlp_vault, h_strat.pubkey(), x_dex, x_atk_mkt, p_scam_l, x_hlp_fee_tok, mint, x_vault, TOKEN_PROGRAM_ID, x_hlp_pfl, x_hlp_pda, prog_id, 0), &payer, &[&payer, &h_strat], 508, "16C-3: HlpTakeoverLiquidate rejects unlisted M_atk");

        // 16D: `mode = 2/3` Hand-Off Trade-Fee Bypass FIXED!
        //   First clear dead legs from 16A (`ClearDeadLeg` frees `p_btc_s` completely; refresh `p_scam_l` on x_atk_mkt)!
        send_ok(&mut svm, ix_clear_dead_leg(prog_id, x_dex, x_btc_mkt, p_btc_s), &payer, &[&payer]);
        send_ok(&mut svm, ix_clear_dead_leg(prog_id, x_dex, x_atk_mkt, p_scam_l), &payer, &[&payer]);
        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, x_dex, x_atk_mkt, p_scam_l, false)], &payer, &[&payer]);
        //   Open Long 2.0 on `p_btc_s` vs Short 2.0 on `p_scam_l` on `x_fee_mkt` (`tradeFeeBps = 50` = 0.50%).
        //   Then hand off Long 2.0 (`mode = 2`) to `p_atk` (re-funded): `p_atk` MUST pay exact 0.50% = $1.00 fee!
        //   Then hand off Short 2.0 (`mode = 3`) from `p_scam_l` to `p_btc_s`: `p_btc_s` MUST pay exact 0.50% = $1.00 fee!
        send_ok(&mut svm, ix_deposit_collateral(prog_id, x_dex, p_atk, p_atk_kp.pubkey(), p_atk_tok, mint, x_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &p_atk_kp]);
        send_ok(&mut svm, ix_trade(prog_id, x_dex, x_fee_mkt, p_btc_s, p_btc_s_kp.pubkey(), p_scam_l, p_scam_l_kp.pubkey(), 0, 2 * POS_SCALE), &payer, &[&payer, &p_btc_s_kp, &p_scam_l_kp]);
        let fee_ins_0 = read_u64(&svm, &x_fee_mkt, 224); // $1 + $1 = $2 from mode=0 open
        assert_eq!(fee_ins_0, 2 * POS_SCALE);
        // Mode 2 (L->L hand-off: p_btc_s exits Long 2.0, p_atk enters Long 2.0) -> p_atk pays $1.00 tradeFee!
        send_ok(&mut svm, ix_trade(prog_id, x_dex, x_fee_mkt, p_btc_s, p_btc_s_kp.pubkey(), p_atk, p_atk_kp.pubkey(), 2, 2 * POS_SCALE), &payer, &[&payer, &p_btc_s_kp, &p_atk_kp]);
        assert_eq!(read_u64(&svm, &x_fee_mkt, 224), 3 * POS_SCALE, "16D: mode=2 hand-off MUST charge tradeFeeBps to incoming opening buyer!");
        // Mode 3 (S->S hand-off: p_scam_l exits Short 2.0, p_btc_s enters Short 2.0) -> p_btc_s pays $1.00 tradeFee!
        send_ok(&mut svm, ix_trade(prog_id, x_dex, x_fee_mkt, p_scam_l, p_scam_l_kp.pubkey(), p_btc_s, p_btc_s_kp.pubkey(), 3, 2 * POS_SCALE), &payer, &[&payer, &p_scam_l_kp, &p_btc_s_kp]);
        assert_eq!(read_u64(&svm, &x_fee_mkt, 224), 4 * POS_SCALE, "16D: mode=3 hand-off MUST charge tradeFeeBps to incoming opening buyer!");

        // 16E: Hyperliquid-UX Capital Efficiency + Safety Under -20% Crash (4x deeper than Isolated Margin cliff!)
        //   Alice deposits $100 (exact ∑ IM = $50 BTC + $50 ETH, 10x gross leverage!).
        //   Isolated margin ($50/leg) would LIQUIDATE Long BTC at -5% ($95).
        //   Firewall Cross-Margin survives a full -20% crash ($100 -> $80) with EXACT $100 capital intact,
        //   0 liquidation, $20 freed excess equity immediately crossable into a 3rd market (SOL) without closing!
        let hl_btc_orc = Keypair::new();
        let hl_eth_orc = Keypair::new();
        let hl_sol_orc = Keypair::new();
        let hl_btc = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let hl_eth = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let hl_sol = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        for (m, orc) in [(hl_btc, &hl_btc_orc), (hl_eth, &hl_eth_orc), (hl_sol, &hl_sol_orc)] {
            send_ok(&mut svm, ix_create_market(prog_id, x_dex, m, mint, orc.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 0, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        }
        let hl_u = Keypair::new();
        let hl_mm = Keypair::new();
        svm.airdrop(&hl_u.pubkey(), 10_000_000_000).unwrap();
        svm.airdrop(&hl_mm.pubkey(), 10_000_000_000).unwrap();
        let hl_u_tok = create_tok_acc(&mut svm, &mint, &hl_u.pubkey(), 500 * POS_SCALE);
        let hl_mm_tok = create_tok_acc(&mut svm, &mint, &hl_mm.pubkey(), 5_000 * POS_SCALE);
        let hl_u_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let hl_mm_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        send_ok(&mut svm, ix_init_portfolio(prog_id, x_dex, hl_u_pfl, hl_u.pubkey()), &payer, &[&payer, &hl_u]);
        send_ok(&mut svm, ix_init_portfolio(prog_id, x_dex, hl_mm_pfl, hl_mm.pubkey()), &payer, &[&payer, &hl_mm]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, x_dex, hl_u_pfl, hl_u.pubkey(), hl_u_tok, mint, x_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &hl_u]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, x_dex, hl_mm_pfl, hl_mm.pubkey(), hl_mm_tok, mint, x_vault, TOKEN_PROGRAM_ID, 2_000 * POS_SCALE), &payer, &[&payer, &hl_mm]);
        // Open Long 5 BTC ($500, IM=$50, MM=$25) + Short 5 ETH ($500, IM=$50, MM=$25) on EXACT $100 (100% HL IM efficiency!)
        send_ok(&mut svm, ix_trade(prog_id, x_dex, hl_btc, hl_u_pfl, hl_u.pubkey(), hl_mm_pfl, hl_mm.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &hl_u, &hl_mm]);
        send_ok(&mut svm, ix_trade(prog_id, x_dex, hl_eth, hl_mm_pfl, hl_mm.pubkey(), hl_u_pfl, hl_u.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &hl_mm, &hl_u]);
        assert_eq!(pfl_total_capital(&svm, &hl_u_pfl), 100 * POS_SCALE);
        assert_eq!(pfl_locked_mm(&svm, &hl_u_pfl), 50 * POS_SCALE);
        assert_eq!(pfl_free_capital(&svm, &hl_u_pfl), 50 * POS_SCALE);
        // Crash BOTH BTC and ETH -20% in 5% tranches ($100 -> $95 -> $90 -> $85 -> $80) — 4x past Isolated Margin liquidation!
        for target in [95 * POS_SCALE, 90 * POS_SCALE, 85 * POS_SCALE, 80 * POS_SCALE] {
            step_two_oracles(&mut svm, prog_id, hl_btc, &hl_btc_orc, hl_eth, &hl_eth_orc, target, &payer);
            // MM settles losing ETH Long -> funds R_ETH; Alice atomically runs [RefreshLeg(ETH), RefreshLeg(BTC)]!
            send_ok(&mut svm, ix_refresh_leg(prog_id, x_dex, hl_eth, hl_mm_pfl, false), &payer, &[&payer]);
            send_ixs_ok(&mut svm, &[
                ix_refresh_leg(prog_id, x_dex, hl_eth, hl_u_pfl, false),
                ix_refresh_leg(prog_id, x_dex, hl_btc, hl_u_pfl, false),
            ], &payer, &[&payer]);
            assert_eq!(pfl_total_capital(&svm, &hl_u_pfl), 100 * POS_SCALE, "16E: Hedged spread preserves EXACT $100 across -20% crash!");
        }
        // At $80: totalIm = $40 BTC + $40 ETH = $80, totalLockedMm = $20 + $20 = $40, freeCap = $60 -> $20 freed excess!
        // Alice IMMEDIATELY opens Long 2 SOL ($200 notional, IM=$20, MM=$10) WITHOUT closing BTC or ETH!
        assert_eq!(pfl_locked_mm(&svm, &hl_u_pfl), 40 * POS_SCALE, "16E: Downsized notional automatically released $10 lockedMm back to freeCap!");
        assert_eq!(pfl_free_capital(&svm, &hl_u_pfl), 60 * POS_SCALE);
        let sl_16e = get_slot(&svm) + 1;
        set_slot(&mut svm, sl_16e);
        send_ok(&mut svm, ix_update_oracle(prog_id, hl_sol, hl_sol_orc.pubkey(), 100 * POS_SCALE, 0, 0), &payer, &[&payer, &hl_sol_orc]);
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, x_dex, hl_btc, hl_u_pfl, false),
            ix_refresh_leg(prog_id, x_dex, hl_eth, hl_u_pfl, false),
            ix_refresh_leg(prog_id, x_dex, hl_btc, hl_mm_pfl, false),
            ix_refresh_leg(prog_id, x_dex, hl_eth, hl_mm_pfl, false),
            ix_trade(prog_id, x_dex, hl_sol, hl_u_pfl, hl_u.pubkey(), hl_mm_pfl, hl_mm.pubkey(), 0, 2 * POS_SCALE),
        ], &payer, &[&payer, &hl_u, &hl_mm]);
        assert_eq!(read_u8(&svm, &hl_u_pfl, 4), 3, "16E: Alice opened 3rd leg (Long $200 SOL) using released cross-margin WITHOUT closing BTC/ETH!");
        assert_eq!(pfl_total_capital(&svm, &hl_u_pfl), 100 * POS_SCALE);
        assert_dex_invariants(&svm, &x_dex, &x_vault, &[x_btc_mkt, x_atk_mkt, x_fee_mkt, hl_btc, hl_eth, hl_sol], &[p_atk, p_btc_s, p_scam_l, x_hlp_pfl, hl_u_pfl, hl_mm_pfl], "16E-final");
    }
    println!("[PASS] Suite 16: Full Red-Team + HL-UX Capital Efficiency Regressions (16A M_atk->I_BTC Defeated, 16B PropAMM Allowlist, 16C HLP Rugs Blocked, 16D Mode 2/3 Fee, 16E -20% Hedged Survival & 3rd-Leg Cross Reuse!)");

    // =========================================================================
    // SUITE 17: STRICT ABI DUP-STUB ATTACK REGRESSIONS (17A) +
    //           5,000-STEP MULTI-PROGRAM ADVERSARIAL STATEFUL FUZZER (17B)
    //   Drives ALL 5 production .so binaries (`percolator.so`, `matcher.so`,
    //   `hlp_vault.so`, `reward_module.so`, `oracle_adapter.so`) + `evil_matcher.so`
    //   simultaneously under randomized adversarial sequences, asserting:
    //     - Exact 5-bucket stock equality `V == C + I + R + S + F` + `real_vault >= V`
    //     - `p.totalLockedMm == Σ_j p.leg[j].lockedMm` for EVERY portfolio
    //     - Honest `I_BTC` NEVER loses 1 atom despite `M_atk` pumps & K+1=5 bursts!
    //     - `HlpVault` share conservation & zero strategist rug!
    //     - `RewardModule` 3-bucket quote escrow conservation (`vault >= active + rollover + pending`)!
    // =========================================================================
    {
        // --- 17A: Strict ABI Dup-Stub Attack Regressions across core & external programs ---
        let a_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (a_vault, a_vbump) = derive_dex_vault(&prog_id, &a_dex);
        // 17A-1: `InitDex` with `feeVault == admin` (duplicate stub!) -> REJECTED Custom(109) (`PErr.aliasedAccounts`)!
        send_err_custom(&mut svm, ix_init_dex(prog_id, a_dex, dex_admin.pubkey(), mint, a_vault, dex_admin.pubkey(), TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, a_vbump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin], 109, "17A-1: InitDex rejects dup feeVault==admin");
        // Valid InitDex succeeds:
        send_ok(&mut svm, ix_init_dex(prog_id, a_dex, dex_admin.pubkey(), mint, a_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, a_vbump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let a_sl = get_slot(&svm) + 10;
        set_slot(&mut svm, a_sl);

        // 17A-2: `CreateMarket` with unauthorized dup `feeVaultTok == dex` (dup idx 0!) -> REJECTED Custom(109)!
        let a_mkt_bad = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        send_err_custom(&mut svm, ix_create_market(prog_id, a_dex, a_mkt_bad, mint, dex_admin.pubkey(), dex_admin.pubkey(), admin_tok, a_dex, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 10, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin], 109, "17A-2: CreateMarket rejects dup feeVaultTok==dex");
        // 17A-3: `CreateMarket` with legitimate `creator == oracleAuth` (idx 3) AND `feeVaultTok == creatorTok` (idx 5) via `resolveDup` -> SUCCEEDS!
        let a_mkt_alias = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        send_ok(&mut svm, ix_create_market(prog_id, a_dex, a_mkt_alias, mint, dex_admin.pubkey(), dex_admin.pubkey(), admin_tok, admin_tok, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 10, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);

        // 17A-4: `DepositCollateral` with dup `ownerTok == dex` -> REJECTED Custom(109)!
        let a_u = Keypair::new();
        svm.airdrop(&a_u.pubkey(), 10_000_000_000).unwrap();
        let a_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        send_ok(&mut svm, ix_init_portfolio(prog_id, a_dex, a_pfl, a_u.pubkey()), &payer, &[&payer, &a_u]);
        send_err_custom(&mut svm, ix_deposit_collateral(prog_id, a_dex, a_pfl, a_u.pubkey(), a_dex, mint, a_vault, TOKEN_PROGRAM_ID, POS_SCALE), &payer, &[&payer, &a_u], 109, "17A-4: DepositCollateral rejects dup ownerTok==dex");

        // 17A-5: `CloseAccount([acc, owner, acc])` (dup idx 0!) -> REJECTED Custom(109)!
        //        `CloseAccount([acc, owner, owner])` (legitimate self-refund dup idx 1 via `resolveDup`!) -> SUCCEEDS!
        send_err_custom(&mut svm, ix_close_account(prog_id, a_pfl, a_u.pubkey(), a_pfl), &payer, &[&payer, &a_u], 109, "17A-5a: CloseAccount rejects dest==acc");
        let lam_pre = svm.get_account(&a_u.pubkey()).unwrap().lamports;
        send_ok(&mut svm, ix_close_account(prog_id, a_pfl, a_u.pubkey(), a_u.pubkey()), &payer, &[&payer, &a_u]);
        assert!(svm.get_account(&a_u.pubkey()).unwrap().lamports > lam_pre, "17A-5b: CloseAccount self-refund refunded rent!");

        // 17A-6: `Matcher::InitPropAmm` with dup `owner == ctx` -> REJECTED Custom(109)!
        let a_prop_kp = Keypair::new();
        svm.set_account(a_prop_kp.pubkey(), Account { lamports: 10_000_000, data: vec![0u8; PROP_AMM_SIZE], owner: matcher_prog, executable: false, rent_epoch: 0 }).unwrap();
        send_err_custom(&mut svm, ix_init_prop_amm(matcher_prog, a_prop_kp.pubkey(), a_prop_kp.pubkey(), 0, 20, 10, POS_SCALE, &[1]), &payer, &[&payer, &a_prop_kp], 109, "17A-6: InitPropAmm rejects dup owner==ctx");

        // --- 17B: 5,000-Step Multi-Program Adversarial Stateful Fuzzer ---
        let f_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (f_vault, f_vbump) = derive_dex_vault(&prog_id, &f_dex);
        send_ok(&mut svm, ix_init_dex(prog_id, f_dex, dex_admin.pubkey(), mint, f_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, f_vbump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let mut f_slot = get_slot(&svm) + 10;
        let mut f_ts: i64 = 1_760_000_000;
        {
            let mut clk: Clock = svm.get_sysvar();
            clk.slot = f_slot; clk.unix_timestamp = f_ts;
            svm.set_sysvar(&clk);
        }

        // 3 markets:
        //   0: Honest BTC (driven by `oracle_adapter.so` + wired to `reward_module.so` 50% fee buy-and-burn!)
        //   1: Honest ETH (direct oracle, allowlisted in HLP + Matcher)
        //   2: Adversarial permissionless `M_atk` (NOT allowlisted in HLP or Matcher!)
        let f_rew_cfg = create_prog_acc(&mut svm, &rew_prog, REW_SIZE);
        let (f_rew_pda, f_rew_bump) = derive_rew_auth(&rew_prog, &f_rew_cfg);
        let f_btc_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let (f_btc_orac_pda, f_btc_orac_bump) = Address::find_program_address(&[b"orac", f_btc_adp.as_ref()], &adapter_prog);
        let f_btc_feed = Keypair::new().pubkey();
        let f_btc_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let f_eth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let f_atk_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let f_eth_orc = Keypair::new();
        let f_atk_orc = Keypair::new();

        // Create BTC market with 50% reward split (`rewardBps = 5000`, `tradeFeeBps = 20`) & `oracle_adapter` PDA!
        send_ok(&mut svm, ix_create_market_with_reward(
            prog_id, f_dex, f_btc_mkt, mint, f_btc_orac_pda, dex_admin.pubkey(), admin_tok, fee_vault,
            100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 20, 75, 2500, 1_000_000 * POS_SCALE, 0, 5000, f_rew_pda,
        ), &payer, &[&payer, &dex_admin]);
        // Init `oracle_adapter.so` (Chainlink OCR2 feed) for BTC!
        let mut f_btc_spot_e8: i128 = 10_000_000_000; // $100.00 at 8 decimals
        svm.set_account(f_btc_feed, Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 0, f_slot, f_btc_spot_e8), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
        let mut f_adp_ix = vec![0u8; 28];
        f_adp_ix[0] = 0; f_adp_ix[1] = f_btc_orac_bump; f_adp_ix[2] = 2; // FEED_CHAINLINK
        f_adp_ix[4..12].copy_from_slice(&50u64.to_le_bytes());
        f_adp_ix[12..20].copy_from_slice(&100u64.to_le_bytes());
        send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
            AccountMeta::new(f_btc_adp, false), AccountMeta::new_readonly(dex_admin.pubkey(), true),
            AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(f_btc_mkt, false),
            AccountMeta::new_readonly(f_btc_feed, false),
        ], data: f_adp_ix }, &payer, &[&payer, &dex_admin]);

        // Create ETH & adversarial `M_atk`
        send_ok(&mut svm, ix_create_market(prog_id, f_dex, f_eth_mkt, mint, f_eth_orc.pubkey(), dex_admin.pubkey(), admin_tok, fee_vault, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 15, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &dex_admin]);
        send_ok(&mut svm, ix_create_market(prog_id, f_dex, f_atk_mkt, mint, f_atk_orc.pubkey(), attacker.pubkey(), attacker_tok, fee_vault, 100 * POS_SCALE, 20, 500, 0, 1000, 500, 100, 10, 75, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &attacker]);

        let f_btc_mid = read_u64(&svm, &f_btc_mkt, 8);
        let f_eth_mid = read_u64(&svm, &f_eth_mkt, 8);
        let _f_atk_mid = read_u64(&svm, &f_atk_mkt, 8);

        // Seed honest BTC & ETH insurance (`I_BTC = $1,000`) — MUST NEVER DECREASE BY 1 ATOM!
        let f_lp_tok = create_tok_acc(&mut svm, &mint, &lp.pubkey(), 10_000 * POS_SCALE);
        let f_btc_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        let f_eth_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(&mut svm, ix_deposit_insurance(prog_id, f_dex, f_btc_mkt, f_btc_ins, lp.pubkey(), f_lp_tok, mint, f_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &lp]);
        send_ok(&mut svm, ix_deposit_insurance(prog_id, f_dex, f_eth_mkt, f_eth_ins, lp.pubkey(), f_lp_tok, mint, f_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &lp]);
        let mut f_min_ibtc = read_u64(&svm, &f_btc_mkt, 224);

        // Wire `reward_module.so` to BTC market (`targetMint` = burnable SPL token!)
        let f_t_mint = Keypair::new().pubkey();
        svm.set_account(f_t_mint, Account {
            lamports: 10_000_000,
            data: make_spl_mint(6, 10_000_000_000_000, &dex_admin.pubkey()),
            owner: TOKEN_PROGRAM_ID, executable: false, rent_epoch: 0,
        }).unwrap();
        let f_rew_qvault = create_tok_acc(&mut svm, &mint, &f_rew_pda, 0);
        let f_rew_tescrow = create_tok_acc(&mut svm, &f_t_mint, &f_rew_pda, 0);
        send_ok(&mut svm, ix_init_reward(
            rew_prog, f_rew_cfg, dex_admin.pubkey(), prog_id, f_dex, f_btc_mkt, f_rew_pda,
            mint, f_rew_qvault, TOKEN_PROGRAM_ID, f_t_mint, f_rew_tescrow, TOKEN_PROGRAM_ID,
            None, f_rew_bump, 0, 32, 10_000, POS_SCALE,
        ), &payer, &[&payer, &dex_admin]);

        // Wire `hlp_vault.so` + `matcher.so` allowing ONLY `[BTC, ETH]` (NEVER `M_atk`!) + `evil_matcher.so` ctx
        let f_hlp_vault = create_prog_acc(&mut svm, &hlp_prog, HLP_SIZE);
        let (f_hlp_pda, f_hlp_bump) = Address::find_program_address(&[b"hlpv", f_hlp_vault.as_ref()], &hlp_prog);
        let f_hlp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let f_hlp_fee_tok = create_tok_acc(&mut svm, &mint, &f_hlp_pda, 0);
        send_ok(&mut svm, ix_init_hlp_vault(
            hlp_prog, f_hlp_vault, h_strat.pubkey(), f_dex, f_hlp_pfl, f_hlp_pda, f_hlp_fee_tok, prog_id,
            matcher_prog, f_hlp_bump, 2, 0, POS_SCALE, &[f_btc_mid, f_eth_mid],
        ), &payer, &[&payer, &h_strat]);
        let f_prop_ctx = create_prog_acc(&mut svm, &matcher_prog, PROP_AMM_SIZE);
        send_ok(&mut svm, ix_init_prop_amm(matcher_prog, f_prop_ctx, h_strat.pubkey(), 0, 20, 10, 20 * POS_SCALE, &[f_btc_mid, f_eth_mid]), &payer, &[&payer, &h_strat]);
        send_ok(&mut svm, ix_set_hlp_matcher(hlp_prog, f_hlp_vault, h_strat.pubkey(), f_hlp_pfl, f_hlp_pda, prog_id, Some(f_prop_ctx), None), &payer, &[&payer, &h_strat]);
        let f_evil_ctx = create_prog_acc(&mut svm, &evil_prog, PROP_AMM_SIZE);
        let f_hlp_lps = [Keypair::new(), Keypair::new()];
        let mut f_hlp_recs = Vec::new();
        let mut f_hlp_toks = Vec::new();
        for lpk in &f_hlp_lps {
            svm.airdrop(&lpk.pubkey(), 10_000_000_000).unwrap();
            let rec = create_prog_acc(&mut svm, &hlp_prog, HLP_REC_SIZE);
            let tok = create_tok_acc(&mut svm, &mint, &lpk.pubkey(), 50_000 * POS_SCALE);
            send_ok(&mut svm, ix_deposit_hlp(hlp_prog, f_hlp_vault, rec, lpk.pubkey(), tok, f_dex, f_hlp_pfl, mint, f_vault, TOKEN_PROGRAM_ID, prog_id, 5_000 * POS_SCALE), &payer, &[&payer, lpk]);
            f_hlp_recs.push(rec);
            f_hlp_toks.push(tok);
        }

        // 4 Traders with USDC + target tokens for RewardModule bidding!
        let f_traders: Vec<Keypair> = (0..4).map(|_| Keypair::new()).collect();
        let mut f_pfls = Vec::new();
        let mut f_toks = Vec::new();
        let mut f_btoks = Vec::new();
        for tkp in &f_traders {
            svm.airdrop(&tkp.pubkey(), 10_000_000_000).unwrap();
            let p = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
            let t = create_tok_acc(&mut svm, &mint, &tkp.pubkey(), 50_000 * POS_SCALE);
            let bt = create_tok_acc(&mut svm, &f_t_mint, &tkp.pubkey(), 50_000 * POS_SCALE);
            send_ok(&mut svm, ix_init_portfolio(prog_id, f_dex, p, tkp.pubkey()), &payer, &[&payer, tkp]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, f_dex, p, tkp.pubkey(), t, mint, f_vault, TOKEN_PROGRAM_ID, 2_000 * POS_SCALE), &payer, &[&payer, tkp]);
            f_pfls.push(p);
            f_toks.push(t);
            f_btoks.push(bt);
        }

        let mut f_all_pfls = f_pfls.clone();
        f_all_pfls.push(f_hlp_pfl);
        let f_all_mkts = [f_btc_mkt, f_eth_mkt, f_atk_mkt];

        // Deterministic xorshift64 PRNG for 100% reproducible 5,000-step multi-program fuzzing!
        let mut rng: u64 = 0xDEAD_BEEF_CAFE_2026;
        let mut next_u64 = || -> u64 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };

        let mut f_ok = 0u64;
        let mut f_cranks = 0u64;
        let mut f_matcher_trades = 0u64;
        let mut f_hlp_ops = 0u64;
        let mut f_rew_ops = 0u64;
        let mut f_liqs = 0u64;
        let mut f_adv_blocked = 0u64;
        let mut cur_epoch_acc: Option<(Address, Vec<(usize, Address)>)> = None;

        for step in 0..5_000u64 {
            let r = next_u64();
            let act = r % 20;
            match act {
                // 0..2: Advance slot + crank BTC via `oracle_adapter.so` + step ETH & `M_atk`!
                0..=2 => {
                    f_slot += 1;
                    f_ts += 1;
                    let mut clk: Clock = svm.get_sysvar();
                    clk.slot = f_slot; clk.unix_timestamp = f_ts;
                    svm.set_sysvar(&clk);
                    let dir = (next_u64() % 3) as i128 - 1; // -1, 0, +1
                    let delta_bps = (next_u64() % 75) as i128; // up to 0.74% (inside K+1=5 clamp!)
                    f_btc_spot_e8 = (f_btc_spot_e8 + (f_btc_spot_e8 * dir * delta_bps) / 10_000)
                        .clamp(5_000_000_000, 20_000_000_000);
                    svm.set_account(f_btc_feed, Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, (step % 4) as u32, f_slot, f_btc_spot_e8), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
                    let crank_ix = Instruction { program_id: adapter_prog, accounts: vec![
                        AccountMeta::new_readonly(f_btc_adp, false), AccountMeta::new(f_btc_mkt, false),
                        AccountMeta::new_readonly(f_btc_feed, false), AccountMeta::new_readonly(f_btc_orac_pda, false),
                        AccountMeta::new_readonly(prog_id, false),
                    ], data: vec![1] };
                    if send_ixs_try(&mut svm, &[crank_ix], &payer, &[&payer]).is_ok() {
                        f_ok += 1; f_cranks += 1;
                    }
                    // Step ETH
                    let eth_p = read_u64(&svm, &f_eth_mkt, 112);
                    let eth_d = (eth_p * (next_u64() % 70)) / 10_000;
                    let eth_np = if next_u64() % 2 == 0 { (eth_p + eth_d).min(200 * POS_SCALE) } else { eth_p.saturating_sub(eth_d).max(50 * POS_SCALE) };
                    if send_ixs_try(&mut svm, &[ix_update_oracle(prog_id, f_eth_mkt, f_eth_orc.pubkey(), eth_np, 0, 0)], &payer, &[&payer, &f_eth_orc]).is_ok() {
                        f_ok += 1;
                    }
                    // Step adversarial `M_atk` (extreme max-clamp swings!)
                    let atk_p = read_u64(&svm, &f_atk_mkt, 112);
                    let atk_d = (atk_p * 75) / 10_000;
                    let atk_np = if (step / 25) % 2 == 0 { (atk_p + atk_d).min(250 * POS_SCALE) } else { atk_p.saturating_sub(atk_d).max(20 * POS_SCALE) };
                    if send_ixs_try(&mut svm, &[ix_update_oracle(prog_id, f_atk_mkt, f_atk_orc.pubkey(), atk_np, 0, 0)], &payer, &[&payer, &f_atk_orc]).is_ok() {
                        f_ok += 1;
                    }
                }
                // 3..6: TradeWithMatcher against `hlp_vault.so` + `matcher.so` (single OR 2-market hedged basket, mode=0/1/4!)
                3..=6 => {
                    let ti = (next_u64() % 4) as usize;
                    let mut ixs: Vec<Instruction> = Vec::new();
                    for &m in &f_all_mkts {
                        let mid = read_u64(&svm, &m, 8);
                        if leg_locked_mm_for_mkt(&svm, &f_pfls[ti], mid) > 0 || read_u8(&svm, &f_pfls[ti], 4) > 0 {
                            ixs.push(ix_refresh_leg(prog_id, f_dex, m, f_pfls[ti], false));
                        }
                        if leg_locked_mm_for_mkt(&svm, &f_hlp_pfl, mid) > 0 {
                            ixs.push(ix_refresh_leg(prog_id, f_dex, m, f_hlp_pfl, false));
                        }
                    }
                    // Only include refreshes for actually present legs so bundle doesn't fail on legNotFound:
                    ixs.clear();
                    for &m in &f_all_mkts {
                        let mid = read_u64(&svm, &m, 8);
                        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, m, f_pfls[ti], false)], &payer, &[&payer]);
                        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, m, f_hlp_pfl, false)], &payer, &[&payer]);
                        let _ = mid;
                    }
                    let m_idx = (next_u64() % 2) as usize;
                    let m_addr = if m_idx == 0 { f_btc_mkt } else { f_eth_mkt };
                    let mp = read_u64(&svm, &m_addr, 112);
                    let mode = [0u8, 1u8, 4u8][(next_u64() % 3) as usize];
                    let is_long = next_u64() % 2 == 0;
                    let qty = ((next_u64() % 4) + 1) * POS_SCALE;
                    let lim = if (mode != 1 && is_long) || (mode == 1 && !is_long) { mp + mp / 50 } else { mp.saturating_sub(mp / 50).max(1) };
                    if send_ixs_try(&mut svm, &[ix_trade_with_matcher(prog_id, f_dex, m_addr, f_pfls[ti], f_traders[ti].pubkey(), f_hlp_pfl, matcher_prog, f_prop_ctx, None, mode, is_long, qty, lim)], &payer, &[&payer, &f_traders[ti]]).is_ok() {
                        f_ok += 1; f_matcher_trades += 1;
                    }
                }
                // 7..9: Direct P2P trade across BTC, ETH, or adversarial `M_atk` (mode=0/1/4)
                7..=9 => {
                    let a = (next_u64() % 4) as usize;
                    let b = (a + 1 + (next_u64() % 3) as usize) % 4;
                    let m = f_all_mkts[(next_u64() % 3) as usize];
                    for &mk in &f_all_mkts {
                        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, mk, f_pfls[a], false)], &payer, &[&payer]);
                        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, mk, f_pfls[b], false)], &payer, &[&payer]);
                    }
                    let mode = [0u8, 1u8, 4u8][(next_u64() % 3) as usize];
                    let qty = ((next_u64() % 5) + 1) * POS_SCALE;
                    if send_ixs_try(&mut svm, &[ix_trade(prog_id, f_dex, m, f_pfls[a], f_traders[a].pubkey(), f_pfls[b], f_traders[b].pubkey(), mode, qty)], &payer, &[&payer, &f_traders[a], &f_traders[b]]).is_ok() {
                        f_ok += 1;
                    }
                }
                // 10..11: Deposit / Withdraw collateral on traders
                10..=11 => {
                    let ti = (next_u64() % 4) as usize;
                    let amt = ((next_u64() % 200) + 1) * POS_SCALE;
                    if act == 10 {
                        if send_ixs_try(&mut svm, &[ix_deposit_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_toks[ti], mint, f_vault, TOKEN_PROGRAM_ID, amt)], &payer, &[&payer, &f_traders[ti]]).is_ok() {
                            f_ok += 1;
                        }
                    } else {
                        for &mk in &f_all_mkts {
                            let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, mk, f_pfls[ti], false)], &payer, &[&payer]);
                        }
                        if send_ixs_try(&mut svm, &[ix_withdraw_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_toks[ti], mint, f_vault, TOKEN_PROGRAM_ID, amt)], &payer, &[&payer, &f_traders[ti]]).is_ok() {
                            f_ok += 1;
                        }
                    }
                }
                // 12..13: Liquidations (HLP takeover on BTC/ETH OR fallback on any market!) + ClearDeadLeg
                12..=13 => {
                    let ti = (next_u64() % 4) as usize;
                    let m = f_all_mkts[(next_u64() % 3) as usize];
                    for &mk in &f_all_mkts {
                        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, mk, f_pfls[ti], false)], &payer, &[&payer]);
                    }
                    if act == 12 && m != f_atk_mkt {
                        if send_ixs_try(&mut svm, &[ix_hlp_takeover_liquidate(hlp_prog, f_hlp_vault, h_strat.pubkey(), f_dex, m, f_pfls[ti], f_hlp_fee_tok, mint, f_vault, TOKEN_PROGRAM_ID, f_hlp_pfl, f_hlp_pda, prog_id, 0)], &payer, &[&payer, &h_strat]).is_ok() {
                            f_ok += 1; f_liqs += 1; f_hlp_ops += 1;
                        }
                    } else if send_ixs_try(&mut svm, &[ix_liquidate(prog_id, f_dex, m, f_pfls[ti], keeper_tok, mint, f_vault, TOKEN_PROGRAM_ID)], &payer, &[&payer]).is_ok() {
                        f_ok += 1; f_liqs += 1;
                    }
                    let _ = send_ixs_try(&mut svm, &[ix_clear_dead_leg(prog_id, f_dex, m, f_pfls[ti])], &payer, &[&payer]);
                }
                // 14..15: `hlp_vault.so` passive LP deposit & withdraw!
                14..=15 => {
                    let li = (next_u64() % 2) as usize;
                    for &mk in &[f_btc_mkt, f_eth_mkt] {
                        let _ = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, mk, f_hlp_pfl, false)], &payer, &[&payer]);
                    }
                    if act == 14 {
                        let amt = ((next_u64() % 100) + 1) * POS_SCALE;
                        if send_ixs_try(&mut svm, &[ix_deposit_hlp(hlp_prog, f_hlp_vault, f_hlp_recs[li], f_hlp_lps[li].pubkey(), f_hlp_toks[li], f_dex, f_hlp_pfl, mint, f_vault, TOKEN_PROGRAM_ID, prog_id, amt)], &payer, &[&payer, &f_hlp_lps[li]]).is_ok() {
                            f_ok += 1; f_hlp_ops += 1;
                        }
                    } else {
                        let cur_sh = read_u64(&svm, &f_hlp_recs[li], 72);
                        if cur_sh > 10 * POS_SCALE {
                            let burn = (cur_sh / 10).max(1);
                            if send_ixs_try(&mut svm, &[ix_withdraw_hlp(hlp_prog, f_hlp_vault, f_hlp_recs[li], f_hlp_lps[li].pubkey(), f_hlp_toks[li], f_dex, f_hlp_pfl, f_hlp_pda, mint, f_vault, TOKEN_PROGRAM_ID, prog_id, burn)], &payer, &[&payer, &f_hlp_lps[li]]).is_ok() {
                                f_ok += 1; f_hlp_ops += 1;
                            }
                        }
                    }
                }
                // 16..17: `reward_module.so` full lifecycle (`StartEpoch -> SubmitBid -> SettleEpoch -> ClaimQuote`)!
                16..=17 => {
                    if let Some((ep_acc, ref mut bids)) = cur_epoch_acc {
                        let settled = read_u8(&svm, &ep_acc, 4);
                        let end_slot = read_u64(&svm, &ep_acc, 88);
                        if settled == 0 && f_slot < end_slot {
                            let bi = (next_u64() % 4) as usize;
                            let rec = if let Some((_, r)) = bids.iter().find(|(idx, _)| *idx == bi) {
                                *r
                            } else {
                                let r = create_prog_acc(&mut svm, &rew_prog, BID_SIZE);
                                bids.push((bi, r));
                                r
                            };
                            let b_amt = ((next_u64() % 50) + 1) * POS_SCALE;
                            if send_ixs_try(&mut svm, &[ix_submit_bid(rew_prog, f_rew_cfg, ep_acc, rec, f_traders[bi].pubkey(), f_btoks[bi], f_rew_tescrow, f_t_mint, TOKEN_PROGRAM_ID, b_amt)], &payer, &[&payer, &f_traders[bi]]).is_ok() {
                                f_ok += 1; f_rew_ops += 1;
                            }
                        } else if settled == 0 && f_slot >= end_slot {
                            if send_ixs_try(&mut svm, &[ix_settle_epoch(rew_prog, f_rew_cfg, ep_acc, f_rew_pda, f_rew_tescrow, f_t_mint, TOKEN_PROGRAM_ID, None)], &payer, &[&payer]).is_ok() {
                                f_ok += 1; f_rew_ops += 1;
                            }
                        } else {
                            // Claim all bids from settled epoch, then clear for next epoch!
                            for &(bi, rec) in bids.iter() {
                                if send_ixs_try(&mut svm, &[ix_claim_quote(rew_prog, f_rew_cfg, ep_acc, rec, f_traders[bi].pubkey(), f_rew_pda, f_rew_qvault, f_toks[bi], mint, TOKEN_PROGRAM_ID)], &payer, &[&payer, &f_traders[bi]]).is_ok() {
                                    f_ok += 1; f_rew_ops += 1;
                                }
                            }
                            cur_epoch_acc = None;
                        }
                    } else {
                        let new_ep = create_prog_acc(&mut svm, &rew_prog, EPOCH_SIZE);
                        if send_ixs_try(&mut svm, &[ix_start_epoch(rew_prog, f_rew_cfg, new_ep, f_dex, f_btc_mkt, f_rew_pda, mint, f_vault, f_rew_qvault, TOKEN_PROGRAM_ID, prog_id)], &payer, &[&payer]).is_ok() {
                            cur_epoch_acc = Some((new_ep, Vec::new()));
                            f_ok += 1; f_rew_ops += 1;
                        }
                    }
                }
                // 18..19: Adversarial attack probes (MUST ALL BE REJECTED!)
                _ => {
                    let probe = next_u64() % 4;
                    let ti = (next_u64() % 4) as usize;
                    let res = match probe {
                        0 => // Unlisted `M_atk` through `matcher.so` -> MUST FAIL!
                            send_ixs_try(&mut svm, &[ix_trade_with_matcher(prog_id, f_dex, f_atk_mkt, f_pfls[ti], f_traders[ti].pubkey(), f_hlp_pfl, matcher_prog, f_prop_ctx, None, 0, true, POS_SCALE, 300 * POS_SCALE)], &payer, &[&payer, &f_traders[ti]]),
                        1 => // Strategist binds `evil_matcher.so` -> MUST FAIL!
                            send_ixs_try(&mut svm, &[ix_set_hlp_matcher(hlp_prog, f_hlp_vault, h_strat.pubkey(), f_hlp_pfl, f_hlp_pda, prog_id, Some(f_evil_ctx), None)], &payer, &[&payer, &h_strat]),
                        2 => // Strategist HLP takeover on unlisted `M_atk` -> MUST FAIL!
                            send_ixs_try(&mut svm, &[ix_hlp_takeover_liquidate(hlp_prog, f_hlp_vault, h_strat.pubkey(), f_dex, f_atk_mkt, f_pfls[ti], f_hlp_fee_tok, mint, f_vault, TOKEN_PROGRAM_ID, f_hlp_pfl, f_hlp_pda, prog_id, 0)], &payer, &[&payer, &h_strat]),
                        _ => // Dup-stub attack `DepositCollateral(ownerTok == dex)` -> MUST FAIL!
                            send_ixs_try(&mut svm, &[ix_deposit_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_dex, mint, f_vault, TOKEN_PROGRAM_ID, POS_SCALE)], &payer, &[&payer, &f_traders[ti]]),
                    };
                    assert!(res.is_err(), "Suite 17B adversarial probe {} MUST ALWAYS BE REJECTED at step {}!", probe, step);
                    f_adv_blocked += 1;
                }
            }

            // === CONTINUOUS MULTI-PROGRAM INVARIANT CHECKS AFTER EVERY STEP ===
            // 1. Core DEX 5-bucket stock equality + per-leg `lockedMm` firewall sum + vault SPL backing!
            assert_dex_invariants(&svm, &f_dex, &f_vault, &f_all_mkts, &f_all_pfls, "suite17B-fuzz");
            // 2. Honest `I_BTC` NEVER suffers bad debt or cross-market contagion!
            let cur_ibtc = read_u64(&svm, &f_btc_mkt, 224);
            let cur_ibtc_front = read_u64(&svm, &f_btc_mkt, 232);
            assert!(cur_ibtc + cur_ibtc_front >= f_min_ibtc, "Suite 17B: Honest BTC insurance NAV dropped below initial $1,000! cur={} front={} min={}", cur_ibtc, cur_ibtc_front, f_min_ibtc);
            f_min_ibtc = f_min_ibtc.max(cur_ibtc + cur_ibtc_front).min(cur_ibtc + cur_ibtc_front);
            // 3. `HlpVault` share conservation: sum of LP receipt shares <= totalShares!
            let hlp_tot_sh = read_u64(&svm, &f_hlp_vault, 200);
            let hlp_sum_sh: u64 = f_hlp_recs.iter().map(|r| read_u64(&svm, r, 72)).sum();
            assert!(hlp_sum_sh <= hlp_tot_sh, "Suite 17B: HLP share sum {} > totalShares {}!", hlp_sum_sh, hlp_tot_sh);
            // 4. `RewardModule` 3-bucket quote escrow conservation (`quoteVault >= active + rollover + pending`)!
            let rew_act = read_u64(&svm, &f_rew_cfg, 360);
            let rew_roll = read_u64(&svm, &f_rew_cfg, 368);
            let rew_pend = read_u64(&svm, &f_rew_cfg, 376);
            let rew_qbal = token_amount(&svm, &f_rew_qvault);
            assert!(rew_qbal >= rew_act + rew_roll + rew_pend, "Suite 17B: RewardModule quoteVault {} < active({}) + rollover({}) + pending({})!", rew_qbal, rew_act, rew_roll, rew_pend);
        }
        println!(
            "[PASS] Suite 17: Strict ABI Dup-Stub Regressions (17A) + 5,000-Step Multi-Program Adversarial Fuzzer (17B: {} valid txs across ALL 5 .so binaries — cranks={}, matcher={}, hlp={}, reward={}, liqs={}, adv_blocked={}, 0 invariant violations!)",
            f_ok, f_cranks, f_matcher_trades, f_hlp_ops, f_rew_ops, f_liqs, f_adv_blocked
        );
    }

    println!("==================================================================================");
    println!("  ALL 17 PERCOLATOR-LEAN VERIFICATION + BORING EXCHANGE + 8-LEG + REWARD + PROPAMM + FLIP + HLP + RED-TEAM + MULTI-PROGRAM FUZZ SUITES PASSED 100%!");
    println!("==================================================================================");
}
