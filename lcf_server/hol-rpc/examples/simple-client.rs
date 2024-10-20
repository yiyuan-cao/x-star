use hol_rpc::client::Client;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new("localhost:5000")?;
    client.new_type("hprop".to_string(), 0)?;
    let ty = client.parse_type_from_string(":hprop".to_string())?;
    client.new_constant("emp".to_string(), &ty)?;
    let ax = client.new_axiom(&client.parse_term_from_string("emp = true".to_string())?)?;
    let tm = client.parse_term_from_string("emp".to_string())?;
    let tm = client.rewrite(&ax, &tm)?;
    println!("{}", client.string_of_thm(&tm)?);
    Ok(())
}
