// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    data_cache::TransactionDataCache,
    native_functions::{NativeContextExtensions, NativeFunction},
    runtime::VMRuntime,
    session::Session,
};
use move_binary_format::errors::{Location, VMResult};
use move_core_types::{
    account_address::AccountAddress, identifier::Identifier, language_storage::ModuleId,
    resolver::MoveResolver,
};

pub struct MoveVM {
    runtime: VMRuntime,
}

impl MoveVM {
    pub fn new(
        natives: impl IntoIterator<Item = (AccountAddress, Identifier, Identifier, NativeFunction)>,
    ) -> VMResult<Self> {
        Ok(Self {
            runtime: VMRuntime::new(natives).map_err(|err| err.finish(Location::Undefined))?,
        })
    }

    /// Create a new Session backed by the given storage.
    ///
    /// Right now it is the caller's responsibility to ensure cache coherence of the Move VM Loader
    ///   - When a module gets published in a Move VM Session, and then gets used by another
    ///     transaction, it will be loaded into the code cache and stay there even if the resulted
    ///     effects do not get commited back to the storage when the Session ends.
    ///   - As a result, if one wants to have multiple sessions at a time, one needs to make sure
    ///     none of them will try to publish a module. In other words, if there is a module publishing
    ///     Session it must be the only Session existing.
    ///   - In general, a new Move VM needs to be created whenever the storage gets modified by an
    ///     outer envrionment, or otherwise the states may be out of sync. There are a few exceptional
    ///     cases where this may not be necessary, with the most notable one being the common module
    ///     publishing flow: you can keep using the same Move VM if you publish some modules in a Session
    ///     and apply the effects to the storage when the Session ends.
    pub fn new_session<'r, S: MoveResolver>(&self, remote: &'r S) -> Session<'r, '_, S> {
        self.runtime.new_session(remote)
    }

    /// Create a new session, as in `new_session`, but provide native context extensions.
    pub fn new_session_with_extensions<'r, S: MoveResolver>(
        &self,
        remote: &'r S,
        extensions: NativeContextExtensions,
    ) -> Session<'r, '_, S> {
        self.runtime.new_session_with_extensions(remote, extensions)
    }

    /// Load a module into VM's code cache
    pub fn load_module<'r, S: MoveResolver>(
        &self,
        module_id: &ModuleId,
        remote: &'r S,
    ) -> VMResult<()> {
        self.runtime
            .loader()
            .load_module(
                module_id,
                &TransactionDataCache::new(remote, self.runtime.loader()),
            )
            .map(|_| ())
    }
}
