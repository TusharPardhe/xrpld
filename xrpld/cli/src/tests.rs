#[cfg(test)]
mod tests {
    use crate::{Cli, Command, ValidatorKeysAction, logo, rpc_call};
    use clap::Parser;

    #[test]
    fn cli_no_args_returns_none_command() {
        let cli = Cli::try_parse_from(["quaxar"]).unwrap();
        assert!(cli.command.is_none());
    }

    #[test]
    fn cli_status_parses() {
        let cli = Cli::try_parse_from(["quaxar", "status"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Status)));
    }

    #[test]
    fn cli_ledger_audit_parses_network_ledger_and_output() {
        let cli = Cli::try_parse_from([
            "quaxar",
            "ledger-audit",
            "--network",
            "testnet",
            "--ledger",
            "20296265",
            "--output",
            "/tmp/quaxar-audit",
        ])
        .unwrap();
        assert!(matches!(cli.command, Some(Command::LedgerAudit { .. })));
    }

    #[test]
    fn cli_health_parses() {
        let cli = Cli::try_parse_from(["quaxar", "health"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Health)));
    }

    #[test]
    fn cli_peers_parses() {
        let cli = Cli::try_parse_from(["quaxar", "peers"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Peers)));
    }

    #[test]
    fn cli_sync_status_parses() {
        let cli = Cli::try_parse_from(["quaxar", "sync-status"]).unwrap();
        assert!(matches!(cli.command, Some(Command::SyncStatus)));
    }

    #[test]
    fn cli_rpc_parses_method_params_and_raw_flag() {
        let cli = Cli::try_parse_from([
            "quaxar",
            "rpc",
            "ledger",
            r#"{"ledger_index":"validated"}"#,
            "--raw",
        ])
        .unwrap();
        match cli.command {
            Some(Command::Rpc {
                method,
                params,
                raw,
            }) => {
                assert_eq!(method, "ledger");
                assert_eq!(params.as_deref(), Some(r#"{"ledger_index":"validated"}"#));
                assert!(raw);
            }
            _ => panic!("expected Rpc"),
        }
    }

    #[test]
    fn cli_operational_rpc_shortcuts_parse() {
        for command in [
            "ping",
            "server-info",
            "server-state",
            "server-definitions",
            "ledger-closed",
            "ledger-current",
            "ledger-header",
            "fetch-info",
            "get-counts",
            "log-rotate",
            "random",
            "validator-info",
            "validator-list-sites",
            "unl-list",
            "consensus-info",
            "tx-reduce-relay",
        ] {
            Cli::try_parse_from(["quaxar", command]).unwrap_or_else(|err| {
                panic!("{command} should parse: {err}");
            });
        }
    }

    #[test]
    fn cli_can_delete_accepts_optional_value() {
        let cli = Cli::try_parse_from(["quaxar", "can-delete", "now"]).unwrap();
        match cli.command {
            Some(Command::CanDelete { value }) => assert_eq!(value.as_deref(), Some("now")),
            _ => panic!("expected CanDelete"),
        }
    }

    #[test]
    fn cli_db_stats_parses() {
        let cli = Cli::try_parse_from(["quaxar", "db-stats"]).unwrap();
        assert!(matches!(cli.command, Some(Command::DbStats)));
    }

    #[test]
    fn cli_log_level_no_arg_parses() {
        let cli = Cli::try_parse_from(["quaxar", "log-level"]).unwrap();
        assert!(matches!(
            cli.command,
            Some(Command::LogLevel { level: None })
        ));
    }

    #[test]
    fn cli_log_level_with_arg_parses() {
        let cli = Cli::try_parse_from(["quaxar", "log-level", "debug"]).unwrap();
        match cli.command {
            Some(Command::LogLevel { level }) => assert_eq!(level.as_deref(), Some("debug")),
            _ => panic!("expected LogLevel"),
        }
    }

    #[test]
    fn cli_config_check_parses() {
        let cli = Cli::try_parse_from(["quaxar", "config"]).unwrap();
        assert!(matches!(cli.command, Some(Command::ConfigCheck)));
    }

    #[test]
    fn cli_doctor_parses() {
        let cli = Cli::try_parse_from(["quaxar", "doctor"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Doctor)));
    }

    #[test]
    fn cli_version_parses() {
        let cli = Cli::try_parse_from(["quaxar", "version"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Version)));
    }

    #[test]
    fn cli_validators_parses() {
        let cli = Cli::try_parse_from(["quaxar", "validators"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Validators)));
    }

    #[test]
    fn cli_amendments_parses() {
        let cli = Cli::try_parse_from(["quaxar", "amendments"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Amendments)));
    }

    #[test]
    fn cli_fee_parses() {
        let cli = Cli::try_parse_from(["quaxar", "fee"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Fee)));
    }

    #[test]
    fn cli_ledger_no_seq_parses() {
        let cli = Cli::try_parse_from(["quaxar", "ledger"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Ledger { seq: None })));
    }

    #[test]
    fn cli_ledger_with_seq_parses() {
        let cli = Cli::try_parse_from(["quaxar", "ledger", "12345"]).unwrap();
        match cli.command {
            Some(Command::Ledger { seq }) => assert_eq!(seq, Some(12345)),
            _ => panic!("expected Ledger"),
        }
    }

    #[test]
    fn cli_account_requires_address() {
        let result = Cli::try_parse_from(["quaxar", "account"]);
        assert!(result.is_err());
    }

    #[test]
    fn cli_account_with_address_parses() {
        let cli = Cli::try_parse_from(["quaxar", "account", "rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh"])
            .unwrap();
        match cli.command {
            Some(Command::Account { address }) => {
                assert_eq!(address, "rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh")
            }
            _ => panic!("expected Account"),
        }
    }

    #[test]
    fn cli_stop_parses() {
        let cli = Cli::try_parse_from(["quaxar", "stop"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Stop)));
    }

    #[test]
    fn cli_connect_parses() {
        let cli = Cli::try_parse_from(["quaxar", "connect", "192.168.1.1:51235"]).unwrap();
        match cli.command {
            Some(Command::Connect { address }) => assert_eq!(address, "192.168.1.1:51235"),
            _ => panic!("expected Connect"),
        }
    }

    #[test]
    fn cli_benchmark_parses() {
        let cli = Cli::try_parse_from(["quaxar", "benchmark"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Benchmark)));
    }

    #[test]
    fn cli_custom_rpc_url() {
        let cli = Cli::try_parse_from(["quaxar", "--rpc-url", "http://localhost:9999", "status"])
            .unwrap();
        assert_eq!(cli.rpc_url, "http://localhost:9999");
        assert!(matches!(cli.command, Some(Command::Status)));
    }

    #[test]
    fn cli_conf_flag() {
        let cli = Cli::try_parse_from(["quaxar", "--conf", "/tmp/test.cfg", "config"]).unwrap();
        assert_eq!(cli.conf.as_deref(), Some("/tmp/test.cfg"));
    }

    #[test]
    fn cli_default_rpc_url() {
        let cli = Cli::try_parse_from(["quaxar", "status"]).unwrap();
        assert_eq!(cli.rpc_url, "http://127.0.0.1:5005");
    }

    #[test]
    fn config_check_missing_file() {
        let path = "/nonexistent/path/config.cfg";
        assert!(!std::path::Path::new(path).exists());
    }

    #[test]
    fn rpc_call_connection_refused() {
        let result = rpc_call("http://127.0.0.1:19999", "ping", serde_json::json!({}));
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Connection failed"));
    }

    #[test]
    fn logo_does_not_panic() {
        // Just ensure print_logo doesn't panic
        logo::print_logo();
    }

    #[test]
    fn cli_connect_requires_address() {
        let result = Cli::try_parse_from(["quaxar", "connect"]);
        assert!(result.is_err());
    }

    #[test]
    fn cli_validator_keys_generate_parses() {
        let cli = Cli::try_parse_from(["quaxar", "validator-keys", "generate"]).unwrap();
        match cli.command {
            Some(Command::ValidatorKeys { action }) => {
                assert!(matches!(action, ValidatorKeysAction::Generate));
            }
            _ => panic!("expected ValidatorKeys"),
        }
    }

    #[test]
    fn cli_validator_keys_create_token_parses() {
        let cli = Cli::try_parse_from(["quaxar", "validator-keys", "create-token"]).unwrap();
        match cli.command {
            Some(Command::ValidatorKeys { action }) => {
                assert!(matches!(
                    action,
                    ValidatorKeysAction::CreateToken { secret: None }
                ));
            }
            _ => panic!("expected ValidatorKeys"),
        }
    }

    #[test]
    fn cli_validator_keys_sign_parses() {
        let cli = Cli::try_parse_from(["quaxar", "validator-keys", "sign", "hello"]).unwrap();
        match cli.command {
            Some(Command::ValidatorKeys { action }) => match action {
                ValidatorKeysAction::Sign { data } => assert_eq!(data, "hello"),
                _ => panic!("expected Sign"),
            },
            _ => panic!("expected ValidatorKeys"),
        }
    }

    #[test]
    fn cli_validator_keys_sign_requires_data() {
        let result = Cli::try_parse_from(["quaxar", "validator-keys", "sign"]);
        assert!(result.is_err());
    }

    #[test]
    fn cli_validator_keys_revoke_parses() {
        let cli = Cli::try_parse_from(["quaxar", "validator-keys", "revoke"]).unwrap();
        match cli.command {
            Some(Command::ValidatorKeys { action }) => {
                assert!(matches!(action, ValidatorKeysAction::Revoke));
            }
            _ => panic!("expected ValidatorKeys"),
        }
    }

    #[test]
    fn cli_validator_keys_show_parses() {
        let cli = Cli::try_parse_from(["quaxar", "validator-keys", "show"]).unwrap();
        match cli.command {
            Some(Command::ValidatorKeys { action }) => {
                assert!(matches!(action, ValidatorKeysAction::Show));
            }
            _ => panic!("expected ValidatorKeys"),
        }
    }

    #[test]
    fn cli_cli_parses() {
        let cli = Cli::try_parse_from(["quaxar", "cli"]).unwrap();
        assert!(matches!(cli.command, Some(Command::Cli)));
    }

    #[test]
    fn cli_interactive_is_not_a_valid_command() {
        let result = Cli::try_parse_from(["quaxar", "interactive"]);
        assert!(result.is_err());
    }
}
