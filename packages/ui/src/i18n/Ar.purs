-- | Arabic UI Translations
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/i18n/ar.ts
module Forge.UI.I18n.Ar
  ( dict
  ) where

import Prelude

import Foreign.Object (Object)
import Foreign.Object as Object

-- | Arabic translation dictionary
dict :: Object String
dict = Object.fromFoldable
  -- Session Review
  [ "ui.sessionReview.title" /\ "تغييرات الجلسة"
  , "ui.sessionReview.diffStyle.unified" /\ "موجد"
  , "ui.sessionReview.diffStyle.split" /\ "منقسم"
  , "ui.sessionReview.expandAll" /\ "توسيع الكل"
  , "ui.sessionReview.collapseAll" /\ "طي الكل"
  , "ui.sessionReview.change.added" /\ "مضاف"
  , "ui.sessionReview.change.removed" /\ "محذوف"
  
  -- Line Comment
  , "ui.lineComment.label.prefix" /\ "تعليق على "
  , "ui.lineComment.label.suffix" /\ ""
  , "ui.lineComment.editorLabel.prefix" /\ "جارٍ التعليق على "
  , "ui.lineComment.editorLabel.suffix" /\ ""
  , "ui.lineComment.placeholder" /\ "أضف تعليقًا"
  , "ui.lineComment.submit" /\ "تعليق"
  
  -- Session Turn
  , "ui.sessionTurn.steps.show" /\ "إظهار الخطوات"
  , "ui.sessionTurn.steps.hide" /\ "إخفاء الخطوات"
  , "ui.sessionTurn.summary.response" /\ "استجابة"
  , "ui.sessionTurn.diff.showMore" /\ "إظهار المزيد من التغييرات ({{count}})"
  
  -- Retry
  , "ui.sessionTurn.retry.retrying" /\ "إعادة المحاولة"
  , "ui.sessionTurn.retry.inSeconds" /\ "خلال {{seconds}} ثواني"
  
  -- Status
  , "ui.sessionTurn.status.delegating" /\ "تفويض العمل"
  , "ui.sessionTurn.status.planning" /\ "تخطيط الخطوات التالية"
  , "ui.sessionTurn.status.gatheringContext" /\ "جمع السياق"
  , "ui.sessionTurn.status.searchingCodebase" /\ "البحث في قاعدة التعليمات البرمجية"
  , "ui.sessionTurn.status.searchingWeb" /\ "البحث في الويب"
  , "ui.sessionTurn.status.makingEdits" /\ "إجراء تعديلات"
  , "ui.sessionTurn.status.runningCommands" /\ "تشغيل الأوامر"
  , "ui.sessionTurn.status.thinking" /\ "تفكير"
  , "ui.sessionTurn.status.thinkingWithTopic" /\ "تفكير - {{topic}}"
  , "ui.sessionTurn.status.gatheringThoughts" /\ "جمع الأفكار"
  , "ui.sessionTurn.status.consideringNextSteps" /\ "النظر في الخطوات التالية"
  
  -- Message Part
  , "ui.messagePart.diagnostic.error" /\ "خطأ"
  , "ui.messagePart.title.edit" /\ "تحرير"
  , "ui.messagePart.title.write" /\ "كتابة"
  , "ui.messagePart.option.typeOwnAnswer" /\ "اكتب إجابتك الخاصة"
  , "ui.messagePart.review.title" /\ "مراجعة إجاباتك"
  
  -- List
  , "ui.list.loading" /\ "جارٍ التحميل"
  , "ui.list.empty" /\ "لا توجد نتائج"
  , "ui.list.clearFilter" /\ "مسح عامل التصفية"
  , "ui.list.emptyWithFilter.prefix" /\ "لا توجد نتائج لـ"
  , "ui.list.emptyWithFilter.suffix" /\ ""
  
  -- Message Nav
  , "ui.messageNav.newMessage" /\ "رسالة جديدة"
  
  -- Text Field
  , "ui.textField.copyToClipboard" /\ "نسخ إلى الحافظة"
  , "ui.textField.copyLink" /\ "نسخ الرابط"
  , "ui.textField.copied" /\ "تم النسخ"
  
  -- Image Preview
  , "ui.imagePreview.alt" /\ "معاينة الصورة"
  
  -- Tools
  , "ui.tool.read" /\ "قراءة"
  , "ui.tool.loaded" /\ "تم التحميل"
  , "ui.tool.list" /\ "قائمة"
  , "ui.tool.glob" /\ "Glob"
  , "ui.tool.grep" /\ "Grep"
  , "ui.tool.webfetch" /\ "جلب الويب"
  , "ui.tool.shell" /\ "Shell"
  , "ui.tool.patch" /\ "تصحيح"
  , "ui.tool.todos" /\ "المهام"
  , "ui.tool.todos.read" /\ "قراءة المهام"
  , "ui.tool.questions" /\ "أسئلة"
  , "ui.tool.agent" /\ "وكيل {{type}}"
  
  -- Common (singular/plural)
  , "ui.common.file.one" /\ "ملف"
  , "ui.common.file.other" /\ "ملفات"
  , "ui.common.question.one" /\ "سؤال"
  , "ui.common.question.other" /\ "أسئلة"
  
  -- Common Actions
  , "ui.common.add" /\ "إضافة"
  , "ui.common.cancel" /\ "إلغاء"
  , "ui.common.confirm" /\ "تأكيد"
  , "ui.common.dismiss" /\ "رفض"
  , "ui.common.close" /\ "إغلاق"
  , "ui.common.next" /\ "التالي"
  , "ui.common.submit" /\ "إرسال"
  
  -- Permission
  , "ui.permission.deny" /\ "رفض"
  , "ui.permission.allowAlways" /\ "السماح دائمًا"
  , "ui.permission.allowOnce" /\ "السماح مرة واحدة"
  
  -- Message
  , "ui.message.expand" /\ "توسيع الرسالة"
  , "ui.message.collapse" /\ "طي الرسالة"
  , "ui.message.copy" /\ "نسخ"
  , "ui.message.copied" /\ "تم النسخ!"
  , "ui.message.attachment.alt" /\ "مرفق"
  
  -- Patch
  , "ui.patch.action.deleted" /\ "محذوف"
  , "ui.patch.action.created" /\ "تم الإنشاء"
  , "ui.patch.action.moved" /\ "منقول"
  , "ui.patch.action.patched" /\ "مصحح"
  
  -- Question
  , "ui.question.subtitle.answered" /\ "{{count}} أجيب"
  , "ui.question.answer.none" /\ "(لا توجد إجابة)"
  , "ui.question.review.notAnswered" /\ "(لم يتم الرد)"
  , "ui.question.multiHint" /\ "(حدد كل ما ينطبق)"
  , "ui.question.custom.placeholder" /\ "اكتب إجابتك..."
  ]
