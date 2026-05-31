use lu_match::Bindings;
use std::collections::HashMap;

/// A variable domain: name -> list of values.
pub type VarDomains = HashMap<String, Vec<String>>;

/// Parse a variable spec like "X=a,b,c" into (name, values).
pub fn parse_var_spec(spec: &str) -> Option<(String, Vec<String>)> {
    let (name, vals) = spec.split_once('=')?;
    let name = name.trim().to_string();
    if name.is_empty() {
        return None;
    }
    let values: Vec<String> = vals.split(',').map(|v| v.trim().to_string()).collect();
    Some((name, values))
}

/// Generate the Cartesian product of all variable domains.
pub fn cartesian_product(domains: &VarDomains) -> Vec<Bindings> {
    let keys: Vec<&String> = domains.keys().collect();
    let values: Vec<&Vec<String>> = keys.iter().map(|k| &domains[*k]).collect();

    if keys.is_empty() {
        return vec![Bindings::new()];
    }

    let mut results = Vec::new();
    let mut indices = vec![0usize; keys.len()];

    loop {
        // Build current combination
        let mut bindings = Bindings::new();
        for (i, key) in keys.iter().enumerate() {
            bindings.insert((*key).clone(), values[i][indices[i]].clone());
        }
        results.push(bindings);

        // Increment indices (odometer-style)
        let mut carry = true;
        for i in (0..keys.len()).rev() {
            if carry {
                indices[i] += 1;
                if indices[i] >= values[i].len() {
                    indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            break; // All combinations exhausted
        }
    }
    results
}

/// Generate an integer range [1..=n] as strings (equivalent to BioMake's `$(iota N)`).
pub fn iota(n: usize) -> Vec<String> {
    (1..=n).map(|i| i.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_var_spec() {
        let (name, vals) = parse_var_spec("X=a,b,c").unwrap();
        assert_eq!(name, "X");
        assert_eq!(vals, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_parse_var_spec_spaces() {
        let (name, vals) = parse_var_spec("Y = 1, 2, 3").unwrap();
        assert_eq!(name, "Y");
        assert_eq!(vals, vec!["1", "2", "3"]);
    }

    #[test]
    fn test_parse_var_spec_invalid() {
        assert!(parse_var_spec("noequals").is_none());
        assert!(parse_var_spec("=values").is_none());
    }

    #[test]
    fn test_cartesian_product_single() {
        let mut domains = VarDomains::new();
        domains.insert("X".into(), vec!["a".into(), "b".into()]);
        let result = cartesian_product(&domains);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_cartesian_product_two_vars() {
        let mut domains = VarDomains::new();
        domains.insert("X".into(), vec!["a".into(), "b".into()]);
        domains.insert("Y".into(), vec!["1".into(), "2".into(), "3".into()]);
        let result = cartesian_product(&domains);
        assert_eq!(result.len(), 6); // 2 * 3
    }

    #[test]
    fn test_cartesian_product_empty() {
        let domains = VarDomains::new();
        let result = cartesian_product(&domains);
        assert_eq!(result.len(), 1); // One empty binding
    }

    #[test]
    fn test_cartesian_product_with_template() {
        let mut domains = VarDomains::new();
        domains.insert("S".into(), vec!["s1".into(), "s2".into()]);
        domains.insert("R".into(), vec!["hg38".into()]);
        let combos = cartesian_product(&domains);
        assert_eq!(combos.len(), 2);

        let expanded: Vec<String> = combos
            .iter()
            .map(|b| lu_match::expand_template("align-{S}-{R}.bam", b))
            .collect();
        assert!(expanded.contains(&"align-s1-hg38.bam".to_string()));
        assert!(expanded.contains(&"align-s2-hg38.bam".to_string()));
    }

    #[test]
    fn test_iota() {
        assert_eq!(iota(5), vec!["1", "2", "3", "4", "5"]);
        assert_eq!(iota(0), Vec::<String>::new());
    }
}
