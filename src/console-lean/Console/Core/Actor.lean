/-
  Console.Core.Actor - Lean4 Proofs for Actor Authorization

  Provides formal verification of:
  - Actor type safety (sum type exhaustiveness)
  - Authorization invariants (admin checks)
  - Workspace/Account access properties

  Corresponds to: console-ps/src/Core/Actor.purs
-/

import Console.Core.Types

namespace Console.Core.Actor

open Console.Core.Types

/-! ## Actor Types -/

/-- Account actor properties -/
structure AccountActor where
  accountId : String
  email : String
  deriving Repr

/-- Public actor (unauthenticated) -/
structure PublicActor where
  deriving Repr

/-- User actor properties -/
structure UserActor where
  userId : String
  workspaceId : String
  accountId : String
  role : UserRole
  deriving Repr

/-- System actor properties -/
structure SystemActor where
  workspaceId : String
  deriving Repr

/-- Actor sum type -/
inductive Actor where
  | account : AccountActor → Actor
  | public : PublicActor → Actor
  | user : UserActor → Actor
  | system : SystemActor → Actor
  deriving Repr

/-! ## Type Predicates -/

/-- Check if actor is account type -/
def Actor.isAccount : Actor → Bool
  | .account _ => true
  | _ => false

/-- Check if actor is user type -/
def Actor.isUser : Actor → Bool
  | .user _ => true
  | _ => false

/-- Check if actor is system type -/
def Actor.isSystem : Actor → Bool
  | .system _ => true
  | _ => false

/-- Check if actor is public type -/
def Actor.isPublic : Actor → Bool
  | .public _ => true
  | _ => false

/-! ## Workspace Access -/

/-- Check if actor has workspace access -/
def Actor.hasWorkspace : Actor → Bool
  | .user _ => true
  | .system _ => true
  | _ => false

/-- Get workspace ID if available -/
def Actor.getWorkspace : Actor → Option String
  | .user u => some u.workspaceId
  | .system s => some s.workspaceId
  | _ => none

/-- hasWorkspace implies getWorkspace returns Some -/
theorem has_workspace_implies_some (a : Actor) :
    a.hasWorkspace = true → a.getWorkspace.isSome = true := by
  cases a <;> simp [Actor.hasWorkspace, Actor.getWorkspace, Option.isSome]

/-- User actors always have workspace -/
theorem user_has_workspace (u : UserActor) :
    (Actor.user u).hasWorkspace = true := by
  simp [Actor.hasWorkspace]

/-- System actors always have workspace -/
theorem system_has_workspace (s : SystemActor) :
    (Actor.system s).hasWorkspace = true := by
  simp [Actor.hasWorkspace]

/-! ## Account Access -/

/-- Check if actor has account -/
def Actor.hasAccount : Actor → Bool
  | .account _ => true
  | .user _ => true
  | _ => false

/-- Get account ID if available -/
def Actor.getAccount : Actor → Option String
  | .account a => some a.accountId
  | .user u => some u.accountId
  | _ => none

/-- hasAccount implies getAccount returns Some -/
theorem has_account_implies_some (a : Actor) :
    a.hasAccount = true → a.getAccount.isSome = true := by
  cases a <;> simp [Actor.hasAccount, Actor.getAccount, Option.isSome]

/-! ## Role Authorization -/

/-- Get user role if actor is user -/
def Actor.getRole : Actor → Option UserRole
  | .user u => some u.role
  | _ => none

/-- Check if actor is admin -/
def Actor.isAdmin : Actor → Bool
  | .user u => u.role == .admin
  | _ => false

/-- Admin actors are always users -/
theorem admin_is_user (a : Actor) :
    a.isAdmin = true → a.isUser = true := by
  cases a <;> simp [Actor.isAdmin, Actor.isUser]

/-- Admin users have admin role -/
theorem admin_has_admin_role (a : Actor) (h : a.isAdmin = true) :
    a.getRole = some UserRole.admin := by
  cases a with
  | user u =>
    simp [Actor.isAdmin] at h
    simp [Actor.getRole]
    cases u.role <;> simp_all
  | _ => simp [Actor.isAdmin] at h

/-! ## Authorization Invariants -/

/-- Authorization result type -/
inductive AuthResult (α : Type) where
  | authorized : α → AuthResult α
  | unauthorized : String → AuthResult α
  deriving Repr

/-- Assert admin authorization -/
def assertAdmin (a : Actor) : AuthResult UserActor :=
  match a with
  | .user u =>
    if u.role == .admin then
      .authorized u
    else
      .unauthorized "Action not allowed. Ask your workspace admin to perform this action."
  | _ => .unauthorized "Expected user actor"

/-- assertAdmin on admin user succeeds -/
theorem assert_admin_success (u : UserActor) (h : u.role = .admin) :
    assertAdmin (.user u) = .authorized u := by
  simp [assertAdmin, h]

/-- assertAdmin on member user fails -/
theorem assert_admin_member_fails (u : UserActor) (h : u.role = .member) :
    ∃ msg, assertAdmin (.user u) = .unauthorized msg := by
  simp [assertAdmin, h]
  exact ⟨"Action not allowed. Ask your workspace admin to perform this action.", rfl⟩

/-- assertAdmin on non-user fails -/
theorem assert_admin_non_user_fails (a : Actor) (h : a.isUser = false) :
    ∃ msg, assertAdmin a = .unauthorized msg := by
  cases a <;> simp_all [assertAdmin, Actor.isUser]

/-! ## Actor Type Exhaustiveness -/

/-- Every actor is exactly one type -/
theorem actor_type_exclusive (a : Actor) :
    (a.isAccount && !a.isUser && !a.isSystem && !a.isPublic) ||
    (!a.isAccount && a.isUser && !a.isSystem && !a.isPublic) ||
    (!a.isAccount && !a.isUser && a.isSystem && !a.isPublic) ||
    (!a.isAccount && !a.isUser && !a.isSystem && a.isPublic) := by
  cases a <;> simp [Actor.isAccount, Actor.isUser, Actor.isSystem, Actor.isPublic]

end Console.Core.Actor
