-- | Esperanto UI Translations
-- |
-- | Esperanto translation dictionary for the UI package.
-- | Contains all UI-related translation keys translated to Esperanto.
-- |
-- | Note: Esperanto added as an additional language beyond the original source.
module Forge.UI.I18n.Eo
  ( dict
  ) where

import Prelude

import Foreign.Object (Object)
import Foreign.Object as Object

-- | Esperanto translation dictionary
dict :: Object String
dict = Object.fromFoldable
  -- Session Review
  [ "ui.sessionReview.title" /\ "Sesiaj sxangxoj"
  , "ui.sessionReview.diffStyle.unified" /\ "Unuigita"
  , "ui.sessionReview.diffStyle.split" /\ "Dividita"
  , "ui.sessionReview.expandAll" /\ "Malfaldi cxiujn"
  , "ui.sessionReview.collapseAll" /\ "Faldi cxiujn"
  , "ui.sessionReview.change.added" /\ "Aldonita"
  , "ui.sessionReview.change.removed" /\ "Forigita"
  
  -- Line Comment
  , "ui.lineComment.label.prefix" /\ "Komento pri "
  , "ui.lineComment.label.suffix" /\ ""
  , "ui.lineComment.editorLabel.prefix" /\ "Komentante pri "
  , "ui.lineComment.editorLabel.suffix" /\ ""
  , "ui.lineComment.placeholder" /\ "Aldoni komenton"
  , "ui.lineComment.submit" /\ "Komenti"
  
  -- Session Turn
  , "ui.sessionTurn.steps.show" /\ "Montri pasxojn"
  , "ui.sessionTurn.steps.hide" /\ "Kasxi pasxojn"
  , "ui.sessionTurn.summary.response" /\ "Respondo"
  , "ui.sessionTurn.diff.showMore" /\ "Montri pliajn sxangxojn ({{count}})"
  
  -- Retry
  , "ui.sessionTurn.retry.retrying" /\ "reprovante"
  , "ui.sessionTurn.retry.inSeconds" /\ "post {{seconds}}s"
  
  -- Status
  , "ui.sessionTurn.status.delegating" /\ "Delegante laboron"
  , "ui.sessionTurn.status.planning" /\ "Planante sekvajn pasxojn"
  , "ui.sessionTurn.status.gatheringContext" /\ "Kolektante kuntekston"
  , "ui.sessionTurn.status.searchingCodebase" /\ "Sercxante en la kodbazo"
  , "ui.sessionTurn.status.searchingWeb" /\ "Sercxante en la reto"
  , "ui.sessionTurn.status.makingEdits" /\ "Farante redaktojn"
  , "ui.sessionTurn.status.runningCommands" /\ "Rulante komandojn"
  , "ui.sessionTurn.status.thinking" /\ "Pensante"
  , "ui.sessionTurn.status.thinkingWithTopic" /\ "Pensante - {{topic}}"
  , "ui.sessionTurn.status.gatheringThoughts" /\ "Kolektante pensojn"
  , "ui.sessionTurn.status.consideringNextSteps" /\ "Konsiderante sekvajn pasxojn"
  
  -- Message Part
  , "ui.messagePart.diagnostic.error" /\ "Eraro"
  , "ui.messagePart.title.edit" /\ "Redakti"
  , "ui.messagePart.title.write" /\ "Skribi"
  , "ui.messagePart.option.typeOwnAnswer" /\ "Tajpu vian propran respondon"
  , "ui.messagePart.review.title" /\ "Revizii viajn respondojn"
  
  -- List
  , "ui.list.loading" /\ "Sxargante"
  , "ui.list.empty" /\ "Neniuj rezultoj"
  , "ui.list.clearFilter" /\ "Viŝi filtrilon"
  , "ui.list.emptyWithFilter.prefix" /\ "Neniuj rezultoj por"
  , "ui.list.emptyWithFilter.suffix" /\ ""
  
  -- Message Nav
  , "ui.messageNav.newMessage" /\ "Nova mesagxo"
  
  -- Text Field
  , "ui.textField.copyToClipboard" /\ "Kopii al tondujo"
  , "ui.textField.copyLink" /\ "Kopii ligilon"
  , "ui.textField.copied" /\ "Kopiita"
  
  -- Image Preview
  , "ui.imagePreview.alt" /\ "Antauvido de bildo"
  
  -- Tools
  , "ui.tool.read" /\ "Legi"
  , "ui.tool.loaded" /\ "Sxargita"
  , "ui.tool.list" /\ "Listo"
  , "ui.tool.glob" /\ "Glob"
  , "ui.tool.grep" /\ "Grep"
  , "ui.tool.webfetch" /\ "Retricevo"
  , "ui.tool.shell" /\ "Sxelo"
  , "ui.tool.patch" /\ "Flikajxo"
  , "ui.tool.todos" /\ "Farindajxoj"
  , "ui.tool.todos.read" /\ "Legi farindajxojn"
  , "ui.tool.questions" /\ "Demandoj"
  , "ui.tool.agent" /\ "{{type}} Agento"
  
  -- Common (singular/plural)
  , "ui.common.file.one" /\ "dosiero"
  , "ui.common.file.other" /\ "dosieroj"
  , "ui.common.question.one" /\ "demando"
  , "ui.common.question.other" /\ "demandoj"
  
  -- Common Actions
  , "ui.common.add" /\ "Aldoni"
  , "ui.common.cancel" /\ "Nuligi"
  , "ui.common.confirm" /\ "Konfirmi"
  , "ui.common.dismiss" /\ "Forigi"
  , "ui.common.close" /\ "Fermi"
  , "ui.common.next" /\ "Sekva"
  , "ui.common.submit" /\ "Sendi"
  
  -- Permission
  , "ui.permission.deny" /\ "Rifuzi"
  , "ui.permission.allowAlways" /\ "Permesi cxiam"
  , "ui.permission.allowOnce" /\ "Permesi unufoje"
  
  -- Message
  , "ui.message.expand" /\ "Malfaldi mesagxon"
  , "ui.message.collapse" /\ "Faldi mesagxon"
  , "ui.message.copy" /\ "Kopii"
  , "ui.message.copied" /\ "Kopiita!"
  , "ui.message.attachment.alt" /\ "aldonajxo"
  
  -- Patch
  , "ui.patch.action.deleted" /\ "Forigita"
  , "ui.patch.action.created" /\ "Kreita"
  , "ui.patch.action.moved" /\ "Movita"
  , "ui.patch.action.patched" /\ "Flikita"
  
  -- Question
  , "ui.question.subtitle.answered" /\ "{{count}} responditaj"
  , "ui.question.answer.none" /\ "(neniu respondo)"
  , "ui.question.review.notAnswered" /\ "(ne respondita)"
  , "ui.question.multiHint" /\ "(elektu cxiujn aplikeblajn)"
  , "ui.question.custom.placeholder" /\ "Tajpu vian respondon..."
  ]
