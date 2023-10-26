use crate::chips::range::range_check::{RangeCheckChip, RangeCheckConfig};
use crate::circuits::traits::CircuitBase;
use crate::merkle_sum_tree::{big_uint_to_fp, Entry};
use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::halo2curves::bn256::Fr as Fp;
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector};
use halo2_proofs::poly::Rotation;
use snark_verifier_sdk::CircuitExt;

#[derive(Clone)]
pub struct SolvencyV2<const N_BYTES: usize, const N_USERS: usize> {
    pub entries: Vec<Entry<1>>,
    pub total_liabilites: Fp,
}

impl<const N_BYTES: usize, const N_USERS: usize> CircuitExt<Fp> for SolvencyV2<N_BYTES, N_USERS> {
    /// Returns the number of public inputs of the circuit. It is 1, namely the total liabilities
    fn num_instance(&self) -> Vec<usize> {
        vec![1]
    }
    /// Returns the values of the public inputs of the circuit.
    fn instances(&self) -> Vec<Vec<Fp>> {
        let instances = vec![self.total_liabilites];
        vec![instances]
    }
}

impl<const N_BYTES: usize, const N_USERS: usize> CircuitBase for SolvencyV2<N_BYTES, N_USERS> {}

impl<const N_BYTES: usize, const N_USERS: usize> SolvencyV2<N_BYTES, N_USERS> {
    pub fn init_empty() -> Self {
        Self {
            entries: vec![Entry::init_empty(); N_USERS as usize],
            total_liabilites: Fp::zero(),
        }
    }

    /// Initializes the circuit with the user entries that are part of the solvency proof
    pub fn init(user_entries: Vec<Entry<1>>, total_liabilites: Fp) -> Self {
        Self {
            entries: user_entries,
            total_liabilites,
        }
    }
}

/// Configuration for the Mst Inclusion circuit
/// # Type Parameters
///
/// * `N_BYTES`: The number of bytes in which the balances should lie
///
/// # Fields
///
/// * `range_check_config`: Configuration for the range check chip
/// * `instance`: Instance column used to store the public inputs
/// * `advices`: Advice columns used to store the private inputs

#[derive(Debug, Clone)]
pub struct SolvencyV2Config<const N_BYTES: usize> {
    range_check_config: RangeCheckConfig<N_BYTES>,
    instance: Column<Instance>,
    advices: [Column<Advice>; 4],
    sum_check_enable_selector: Selector,
}

impl<const N_BYTES: usize> SolvencyV2Config<N_BYTES> {
    pub fn configure(meta: &mut ConstraintSystem<Fp>) -> Self {
        // We need 1 advice column for the username, 1 for the balances, 1 for the accumulated balances and 1 for the range check
        let advices: [Column<Advice>; 4] = std::array::from_fn(|_| meta.advice_column());

        // enable permutation for all the advice columns
        for col in &advices {
            meta.enable_equality(*col);
        }

        // we need a fixed column for the range check and to store the constants
        let fixed_column = meta.fixed_column();
        meta.enable_constant(fixed_column);

        // we also need 1 simple selector for the sum check
        let sum_check_enable_selector = meta.complex_selector();

        // we need 1 complex selector for the range check
        let lookup_enable_selector = meta.complex_selector();

        // Enforce sum constraint
        // cur_acc_sum = prev_acc_sum + cur_balance
        // constraint: cur_acc_sum - prev_acc_sum - cur_balance = 0
        meta.create_gate("sum gate", |meta| {
            let prev_acc_sum = meta.query_advice(advices[2], Rotation::prev());
            let cur_balance = meta.query_advice(advices[1], Rotation::cur());
            let cur_acc_sum = meta.query_advice(advices[2], Rotation::cur());
            let sum_check_selector = meta.query_selector(sum_check_enable_selector);

            vec![sum_check_selector * (prev_acc_sum + cur_balance - cur_acc_sum)]
        });

        let range_check_config = RangeCheckChip::<N_BYTES>::configure(
            meta,
            advices[3],
            fixed_column,
            lookup_enable_selector,
        );

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        Self {
            range_check_config,
            instance,
            advices,
            sum_check_enable_selector,
        }
    }

    /// Assigns the entries to the circuit
    /// At row 0, the username, balance and accumulated balance are set to 0
    /// At row i, the username is set to the username of the i-th entry, the balance is set to the balance of the i-th entry and the accumulated balance is set to the sum of the balances of the first i entries
    /// Enable the sum check selector for each row from 1
    /// Returns the assigned cells for the balances and the accumulated balances
    pub fn assign_entries(
        &self,
        mut layouter: impl Layouter<Fp>,
        entries: &[Entry<1>],
    ) -> Result<(Vec<AssignedCell<Fp, Fp>>, AssignedCell<Fp, Fp>), Error> {
        layouter.assign_region(
            || "assign entries and accumulated balance to table",
            |mut region| {
                let mut accumulated_balance = Fp::zero();

                region.assign_advice_from_constant(
                    || "zero username",
                    self.advices[0],
                    0,
                    Fp::zero(),
                )?;

                region.assign_advice_from_constant(
                    || "zero balance",
                    self.advices[1],
                    0,
                    Fp::zero(),
                )?;

                region.assign_advice_from_constant(
                    || "zero accumulated balance",
                    self.advices[2],
                    0,
                    Fp::zero(),
                )?;

                let mut balances = vec![];
                let mut total_liabilities: Option<AssignedCell<Fp, Fp>> = None;

                for (i, entry) in entries.iter().enumerate() {
                    region.assign_advice(
                        || "username",
                        self.advices[0],
                        i + 1,
                        || Value::known(big_uint_to_fp(entry.username_as_big_uint())),
                    )?;

                    let balance = big_uint_to_fp(&entry.balances()[0]);

                    let balance_assigned = region.assign_advice(
                        || "balance",
                        self.advices[1],
                        i + 1,
                        || Value::known(balance),
                    )?;

                    balances.push(balance_assigned);

                    accumulated_balance += balance;

                    let accumulated_balance_assigned = region.assign_advice(
                        || "accumulated balance",
                        self.advices[2],
                        i + 1,
                        || Value::known(accumulated_balance),
                    )?;

                    if i == entries.len() - 1 {
                        total_liabilities = Some(accumulated_balance_assigned);
                    }

                    self.sum_check_enable_selector.enable(&mut region, i + 1)?;
                }

                Ok((balances, total_liabilities.unwrap()))
            },
        )
    }
}

impl<const N_BYTES: usize, const N_USERS: usize> Circuit<Fp> for SolvencyV2<N_BYTES, N_USERS> {
    type Config = SolvencyV2Config<N_BYTES>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::init_empty()
    }

    /// Configures the circuit
    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        SolvencyV2Config::<N_BYTES>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        // Assign entries
        let (balances, total_liabilities) =
            config.assign_entries(layouter.namespace(|| "assign entries"), &self.entries)?;

        let range_check_chip = RangeCheckChip::<N_BYTES>::construct(config.range_check_config);

        // load range check chip
        range_check_chip.load(&mut layouter)?;

        // Perform range check on the each individual balance and the total liabilities
        // TO DO: assess security implications of not performing range check on the partial accumulated balances
        for i in 0..balances.len() {
            range_check_chip.assign(
                layouter.namespace(|| format!("range check for balance {}", i)),
                &balances[i],
            )?;
        }

        range_check_chip.assign(
            layouter.namespace(|| "range check for total liabilities"),
            &total_liabilities,
        )?;

        // Expose the total liabilities as public input
        self.expose_public(
            layouter.namespace(|| "total liabilities"),
            &total_liabilities,
            0,
            config.instance,
        )?;

        Ok(())
    }
}
