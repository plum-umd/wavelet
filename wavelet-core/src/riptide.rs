//! FFI bindings for the core compiler in Lean,
//! specialized to RipTide.

use lean_sys::{lean_inc, lean_obj_arg, lean_obj_res};
use libc::size_t;
use thiserror::Error;

use crate::ffi::{ensure_init_lean, LeanObject, LeanObjectError};

#[derive(Debug, Error)]
pub enum RipTideError {
    #[error("lean object error: {0}")]
    LeanObjectError(#[from] LeanObjectError),
    #[error("program parsing error: {0}")]
    ProgParseError(String),
    #[error("program validation error: {0}")]
    ProgValidationError(String),
    #[error("dataflow graph parsing error: {0}")]
    ProcParseError(String),
    #[error("dataflow validation error: {0}")]
    ProcValidationError(String),
    #[error("dot format generation error: {0}")]
    DotFormatError(String),
    #[error("handshake generation error: {0}")]
    HandshakeError(String),
    #[error("control-flow lowering failed: {0}")]
    ControlFlowLoweringError(String),
    #[error("value conversion error: {0}")]
    ValueConversionError(String),
    #[error("config not in initial state: {0}")]
    ConfigNotInitial(String),
    #[error("failed to push inputs: {0}")]
    PushInputsError(String),
    #[error("failed to pop outputs: {0}")]
    PopOutputsError(String),
    #[error("config execution error: {0}")]
    ConfigExecError(String),
}

/// A wrapper for `Wavelet.Frontend.RipTide.Prog`.
#[derive(Clone)]
pub struct Prog(LeanObject);

/// A wrapper for `Wavelet.Frontend.RipTide.Proc`.
#[derive(Clone)]
pub struct Proc(LeanObject);

/// A wrapper for `Wavelet.Frontend.RipTide.Value`.
#[derive(Clone)]
pub struct Value(LeanObject);

/// A wrapper for `Wavelet.Frontend.RipTide.Config`.
#[derive(Clone)]
pub struct Config(LeanObject);

/// A wrapper for `Wavelet.Frontend.RipTide.Label`.
pub struct Label(LeanObject);

impl Prog {
    /// Parses a `Prog` from its JSON representation.
    pub fn from_json(json: &str) -> Result<Self, RipTideError> {
        extern "C" {
            fn wavelet_riptide_prog_from_json(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let json = LeanObject::from(json);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_prog_from_json(json.to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(prog) => Ok(Prog(prog)),
            Err(err) => Err(RipTideError::ProgParseError(err.to_str()?.to_string())),
        }
    }

    /// Validates some static properties.
    pub fn validate(&self) -> Result<(), RipTideError> {
        extern "C" {
            fn wavelet_riptide_prog_validate(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_prog_validate(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(_) => Ok(()),
            Err(err) => Err(RipTideError::ProgValidationError(err.to_str()?.to_string())),
        }
    }

    /// Compiles to a `Proc` by lowering control-flow.
    pub fn lower_control_flow(&self) -> Result<Proc, RipTideError> {
        extern "C" {
            fn wavelet_riptide_prog_lower_control_flow(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_prog_lower_control_flow(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(proc) => Ok(Proc(proc)),
            Err(err) => Err(RipTideError::ControlFlowLoweringError(
                err.to_str()?.to_string(),
            )),
        }
    }
}

impl Proc {
    /// Gets the number of atoms
    pub fn num_atoms(&self) -> usize {
        extern "C" {
            fn wavelet_riptide_proc_num_atoms(arg: lean_obj_arg) -> size_t;
        }
        ensure_init_lean();
        unsafe { wavelet_riptide_proc_num_atoms(self.0.clone().to_lean_obj_arg()) as usize }
    }

    /// Gets the number of non-trivial atoms
    pub fn num_non_trivial_atoms(&self) -> usize {
        extern "C" {
            fn wavelet_riptide_proc_num_non_trivial_atoms(arg: lean_obj_arg) -> size_t;
        }
        ensure_init_lean();
        unsafe {
            wavelet_riptide_proc_num_non_trivial_atoms(self.0.clone().to_lean_obj_arg()) as usize
        }
    }

    /// Gets the number of inputs
    pub fn num_inputs(&self) -> usize {
        extern "C" {
            fn wavelet_riptide_proc_num_inputs(arg: lean_obj_arg) -> size_t;
        }
        ensure_init_lean();
        unsafe { wavelet_riptide_proc_num_inputs(self.0.clone().to_lean_obj_arg()) as usize }
    }

    /// Gets the number of outputs
    pub fn num_outputs(&self) -> usize {
        extern "C" {
            fn wavelet_riptide_proc_num_outputs(arg: lean_obj_arg) -> size_t;
        }
        ensure_init_lean();
        unsafe { wavelet_riptide_proc_num_outputs(self.0.clone().to_lean_obj_arg()) as usize }
    }

    /// Parses a `Proc` from its JSON representation.
    pub fn from_json(json: &str) -> Result<Self, RipTideError> {
        extern "C" {
            fn wavelet_riptide_proc_from_json(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let json = LeanObject::from(json);
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_from_json(json.to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(proc) => Ok(Proc(proc)),
            Err(err) => Err(RipTideError::ProcParseError(err.to_str()?.to_string())),
        }
    }

    /// Serializes the `Proc` to its JSON representation.
    pub fn to_json(&self) -> Result<String, RipTideError> {
        extern "C" {
            fn wavelet_riptide_proc_to_json(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_to_json(self.0.clone().to_lean_obj_arg())
        });
        let s: &str = (&res).try_into()?;
        Ok(s.to_string())
    }

    /// Serializes the `Proc` to Graphviz DOT format.
    pub fn to_dot(&self) -> Result<String, RipTideError> {
        extern "C" {
            fn wavelet_riptide_proc_to_dot(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_to_dot(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(dot) => Ok(dot.to_str()?.to_string()),
            Err(err) => Err(RipTideError::DotFormatError(err.to_str()?.to_string())),
        }
    }

    /// Compiles the `Proc` to CIRCT Handshake dialect.
    pub fn to_handshake(&self) -> Result<String, RipTideError> {
        extern "C" {
            fn wavelet_riptide_proc_to_handshake(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_to_handshake(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(hs) => Ok(hs.to_str()?.to_string()),
            Err(err) => Err(RipTideError::HandshakeError(err.to_str()?.to_string())),
        }
    }

    /// Validates some static properties.
    pub fn validate(&self) -> Result<(), RipTideError> {
        extern "C" {
            fn wavelet_riptide_proc_validate(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_validate(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(_) => Ok(()),
            Err(err) => Err(RipTideError::ProcValidationError(err.to_str()?.to_string())),
        }
    }

    /// Removes any redundant unit inputs/outputs.
    pub fn trim_unit_io(&self) -> Proc {
        extern "C" {
            fn wavelet_riptide_proc_trim_unit_io(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_trim_unit_io(self.0.clone().to_lean_obj_arg())
        });
        Proc(res)
    }

    /// Performs various legalizations and optimizations on the dataflow process.
    pub fn optimize<S>(&self, disabled_rules: impl AsRef<[S]>) -> Proc
    where
        S: AsRef<str>,
    {
        extern "C" {
            fn wavelet_riptide_proc_optimize(
                arg: lean_obj_arg,
                disabled_rules: lean_obj_arg,
            ) -> lean_obj_res;
        }
        ensure_init_lean();
        let arr = LeanObject::from(
            disabled_rules
                .as_ref()
                .iter()
                .map(|s| LeanObject::from(s.as_ref()))
                .collect::<Vec<_>>(),
        );
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_proc_optimize(self.0.clone().to_lean_obj_arg(), arr.to_lean_obj_arg())
        });
        Proc(res)
    }
}

impl From<i32> for Value {
    fn from(i: i32) -> Self {
        extern "C" {
            fn wavelet_riptide_value_from_int32(arg: i32) -> lean_obj_res;
        }
        ensure_init_lean();
        Value(LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_value_from_int32(i)
        }))
    }
}

impl TryFrom<Value> for i32 {
    type Error = RipTideError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        extern "C" {
            fn wavelet_riptide_value_to_int32(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_value_to_int32(value.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(i) => Ok(i.try_into()?),
            Err(err) => Err(RipTideError::ValueConversionError(
                err.to_str()?.to_string(),
            )),
        }
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        extern "C" {
            fn wavelet_riptide_value_from_bool(arg: u8) -> lean_obj_res;
        }
        ensure_init_lean();
        Value(LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_value_from_bool(b as u8)
        }))
    }
}

impl TryFrom<Value> for bool {
    type Error = RipTideError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        extern "C" {
            fn wavelet_riptide_value_to_bool(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_value_to_bool(value.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(b) => Ok(b.try_into()?),
            Err(err) => Err(RipTideError::ValueConversionError(
                err.to_str()?.to_string(),
            )),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Ok(i) = i32::try_from(self.clone()) {
            write!(f, "{}", i)
        } else if let Ok(b) = bool::try_from(self.clone()) {
            write!(f, "{}", b)
        } else if self.is_unit() {
            write!(f, "()")
        } else {
            write!(f, "<unknown>")
        }
    }
}

impl Value {
    /// Constructs a unit `Value`.
    pub fn unit() -> Self {
        extern "C" {
            static wavelet_riptide_value_unit: lean_obj_res;
        }
        ensure_init_lean();
        Value(LeanObject::from_lean_obj_res(unsafe {
            // TODO: Check if this is the right way to use a Lean constant.
            lean_inc(wavelet_riptide_value_unit);
            wavelet_riptide_value_unit
        }))
    }

    /// Checks if a `Value` is unit.
    pub fn is_unit(&self) -> bool {
        extern "C" {
            fn wavelet_riptide_value_is_unit(arg: lean_obj_arg) -> u8;
        }
        ensure_init_lean();
        unsafe { wavelet_riptide_value_is_unit(self.0.clone().to_lean_obj_arg()) != 0 }
    }
}

impl Config {
    /// Creates the initial configuration for executing the given `Proc`.
    pub fn new(proc: &Proc) -> Self {
        extern "C" {
            fn wavelet_riptide_config_init(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_init(proc.0.clone().to_lean_obj_arg())
        });
        Config(res)
    }

    /// Checks if the configuration is in its initial state except for the memory.
    pub fn check_init(&self) -> Result<(), RipTideError> {
        extern "C" {
            fn wavelet_riptide_config_check_init(arg: lean_obj_arg) -> lean_obj_arg;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_check_init(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(_) => Ok(()),
            Err(err) => Err(RipTideError::ConfigNotInitial(err.to_str()?.to_string())),
        }
    }

    /// Stores a value into the configuration's memory at the given address.
    pub fn store_mem(&mut self, loc: impl AsRef<str>, addr: &Value, value: &Value) {
        extern "C" {
            fn wavelet_riptide_config_store_mem(
                config: lean_obj_arg,
                loc: lean_obj_arg,
                addr: lean_obj_arg,
                value: lean_obj_arg,
            ) -> lean_obj_res;
        }
        ensure_init_lean();
        self.0 = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_store_mem(
                self.0.clone().to_lean_obj_arg(),
                LeanObject::from(loc.as_ref()).to_lean_obj_arg(),
                addr.0.clone().to_lean_obj_arg(),
                value.0.clone().to_lean_obj_arg(),
            )
        });
    }

    /// Loads a value from the configuration's memory at the given address.
    pub fn load_mem(
        &self,
        loc: impl AsRef<str>,
        addr: &Value,
    ) -> Result<Option<Value>, RipTideError> {
        extern "C" {
            fn wavelet_riptide_config_load_mem(
                config: lean_obj_arg,
                loc: lean_obj_arg,
                addr: lean_obj_arg,
            ) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_load_mem(
                self.0.clone().to_lean_obj_arg(),
                LeanObject::from(loc.as_ref()).to_lean_obj_arg(),
                addr.0.clone().to_lean_obj_arg(),
            )
        });
        match Option::<_>::try_from(&res)? {
            Some(v) => Ok(Some(Value(v))),
            None => Ok(None),
        }
    }

    /// Returns a vector of set memory addresses.
    pub fn mem_addrs(&self, loc: impl AsRef<str>) -> Result<Vec<Value>, RipTideError> {
        extern "C" {
            fn wavelet_riptide_config_mem_addrs(
                config: lean_obj_arg,
                loc: lean_obj_arg,
            ) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_mem_addrs(
                self.0.clone().to_lean_obj_arg(),
                LeanObject::from(loc.as_ref()).to_lean_obj_arg(),
            )
        });
        let arr: Vec<LeanObject> = (&res).try_into()?;
        Ok(arr.into_iter().map(Value).collect())
    }

    /// Returns a vector of used memory names.
    pub fn mem_names(&self) -> Result<Vec<String>, RipTideError> {
        extern "C" {
            fn wavelet_riptide_config_mem_names(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_mem_names(self.0.clone().to_lean_obj_arg())
        });
        let arr: Vec<LeanObject> = (&res).try_into()?;
        Ok(arr
            .into_iter()
            .map(|s| s.to_str().map(|s| s.to_string()))
            .collect::<Result<_, _>>()?)
    }

    /// Pushes one value to each input channel.
    pub fn push_inputs(&mut self, inputs: Vec<Value>) -> Result<(), RipTideError> {
        extern "C" {
            fn wavelet_riptide_config_push_inputs(
                config: lean_obj_arg,
                inputs: lean_obj_arg,
            ) -> lean_obj_res;
        }
        ensure_init_lean();
        let inputs = LeanObject::from(inputs.into_iter().map(|v| v.0).collect::<Vec<LeanObject>>());
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_push_inputs(
                self.0.clone().to_lean_obj_arg(),
                inputs.to_lean_obj_arg(),
            )
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(config) => {
                self.0 = config;
                Ok(())
            }
            Err(err) => Err(RipTideError::PushInputsError(err.to_str()?.to_string())),
        }
    }

    /// Tries to pop one value from each output channel.
    pub fn pop_outputs(&mut self) -> Result<Vec<Value>, RipTideError> {
        extern "C" {
            fn wavelet_riptide_config_pop_outputs(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_pop_outputs(self.0.clone().to_lean_obj_arg())
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(res) => {
                let res: (LeanObject, LeanObject) = (&res).try_into()?;
                let outputs: Vec<LeanObject> = (&res.0).try_into()?;
                let new_config = res.1;
                self.0 = new_config;
                Ok(outputs.into_iter().map(Value).collect())
            }
            Err(err) => Err(RipTideError::PopOutputsError(err.to_str()?.to_string())),
        }
    }

    /// Steps the configuration until stuck or hit the optional step bound.
    pub fn steps(&mut self, bound: Option<usize>) -> Result<Vec<Label>, RipTideError> {
        if bound == Some(0) {
            return Ok(vec![]);
        }
        extern "C" {
            fn wavelet_riptide_config_steps(config: lean_obj_arg, bound: size_t) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_config_steps(self.0.clone().to_lean_obj_arg(), bound.unwrap_or(0))
        });
        match Result::<_, _>::try_from(&res)? {
            Ok(res) => {
                let res: (LeanObject, LeanObject) = (&res).try_into()?;
                let trace: Vec<LeanObject> = (&res.0).try_into()?;
                let new_config = res.1;
                self.0 = new_config;
                Ok(trace.into_iter().map(Label).collect())
            }
            Err(err) => Err(RipTideError::ConfigExecError(err.to_str()?.to_string())),
        }
    }
}

impl Label {
    /// Gets the index of the atom being executed.
    pub fn atom_index(&self) -> usize {
        extern "C" {
            fn wavelet_riptide_label_index(arg: lean_obj_arg) -> size_t;
        }
        ensure_init_lean();
        unsafe { wavelet_riptide_label_index(self.0.clone().to_lean_obj_arg()) as usize }
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        extern "C" {
            fn wavelet_riptide_label_to_string(arg: lean_obj_arg) -> lean_obj_res;
        }
        ensure_init_lean();
        let res = LeanObject::from_lean_obj_res(unsafe {
            wavelet_riptide_label_to_string(self.0.clone().to_lean_obj_arg())
        });
        let s: &str = (&res).try_into().map_err(|_| std::fmt::Error {})?;
        write!(f, "{}", s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_unit() {
        let v_unit = Value::unit();
        let v_true = Value::from(true);
        let v_false = Value::from(false);
        let v_int = Value::from(42i32);

        assert!(v_unit.is_unit());
        assert!(!v_true.is_unit());
        assert!(!v_false.is_unit());
        assert!(!v_int.is_unit());
    }

    #[test]
    fn test_value_bool() {
        assert!(bool::try_from(Value::from(true)).unwrap());
        assert!(!bool::try_from(Value::from(false)).unwrap());
        assert!(bool::try_from(Value::from(0i32)).is_err());
        assert!(bool::try_from(Value::unit()).is_err());
    }

    #[test]
    fn test_value_int32() {
        assert_eq!(i32::try_from(Value::from(123i32)).unwrap(), 123i32);
        assert_eq!(i32::try_from(Value::from(-456i32)).unwrap(), -456i32);
        assert_eq!(i32::try_from(Value::from(i32::MIN)).unwrap(), i32::MIN);
        assert_eq!(i32::try_from(Value::from(i32::MAX)).unwrap(), i32::MAX);
        assert!(i32::try_from(Value::from(true)).is_err());
        assert!(i32::try_from(Value::unit()).is_err());
    }

    #[test]
    fn test_config_init() {
        let proc_json = r#"{"outputs": [], "inputs": [], "atoms": [], "arrays": []}"#;
        let proc = Proc::from_json(proc_json).unwrap();
        let config = Config::new(&proc);
        assert!(config.check_init().is_ok());
    }

    #[test]
    fn test_config_mem() {
        let proc_json = r#"{"outputs": [], "inputs": [], "atoms": [], "arrays": []}"#;
        let proc = Proc::from_json(proc_json).unwrap();
        let mut config = Config::new(&proc);

        for i in 0..10 {
            let addr = Value::from(i);
            let value = Value::from(i * 10);
            config.store_mem("A", &addr, &value);
        }

        for i in 0..10 {
            let addr = Value::from(i);
            let loaded = config.load_mem("A", &addr).unwrap().unwrap();
            let expected = Value::from(i * 10);
            assert_eq!(
                i32::try_from(loaded).unwrap(),
                i32::try_from(expected).unwrap()
            );
        }

        let addrs = config.mem_addrs("A").unwrap();
        assert!(addrs.len() == 10);
        for i in 0..10 {
            assert!(addrs.iter().any(|a| i32::try_from(a.clone()).unwrap() == i));
        }
    }
}
